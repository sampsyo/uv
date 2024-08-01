use std::cmp::Ordering;
use std::fmt;
use std::ops::Bound;
use std::sync::Mutex;
use std::sync::MutexGuard;

use itertools::Either;
use once_cell::sync::Lazy;
use pep440_rs::{Version, VersionSpecifier};
use pubgrub::range::Range;
use rustc_hash::FxHashMap;
use uv_normalize::ExtraName;

use crate::ExtraOperator;
use crate::{MarkerExpression, MarkerOperator, MarkerValueString, MarkerValueVersion};

use super::range::PubGrubSpecifier;

#[derive(Default)]
pub(crate) struct Interner {
    shared: InternerShared,
    state: Mutex<InternerState>,
}

impl InternerShared {
    /// Returns the node, accounting for the negation.
    fn node(&self, id: NodeId) -> &Node {
        &self.nodes[id.index()]
    }
}

impl Interner {
    fn lock(&self) -> InternerGuard<'_> {
        InternerGuard {
            state: self.state.lock().unwrap(),
            shared: &self.shared,
        }
    }

    pub(crate) fn node(&self, id: NodeId) -> &Node {
        self.shared.node(id)
    }

    pub(crate) fn terminal(&self, expr: MarkerExpression) -> NodeId {
        self.lock().terminal(expr)
    }

    pub(crate) fn or(&self, x: NodeId, y: NodeId) -> NodeId {
        self.lock().or(x, y)
    }

    pub(crate) fn and(&self, x: NodeId, y: NodeId) -> NodeId {
        self.lock().and(x, y)
    }

    pub(crate) fn restrict(&self, i: NodeId, f: impl Fn(&Variable) -> Option<bool>) -> NodeId {
        self.lock().restrict(i, &f)
    }

    pub(crate) fn restrict_versions(
        &self,
        i: NodeId,
        f: impl Fn(&Variable) -> Option<Range<Version>>,
    ) -> NodeId {
        self.lock().restrict_versions(i, &f)
    }
}

#[derive(Default)]
struct InternerShared {
    nodes: boxcar::Vec<Node>,
}

#[derive(Default)]
struct InternerState {
    node_ids: FxHashMap<Node, NodeId>,
    cache: FxHashMap<(NodeId, NodeId), NodeId>,
}

pub(crate) static BDD: Lazy<Interner> = Lazy::new(Interner::default);

struct InternerGuard<'a> {
    state: MutexGuard<'a, InternerState>,
    shared: &'a InternerShared,
}

impl InternerGuard<'_> {
    fn create_node(&mut self, var: Variable, children: RangeMap) -> NodeId {
        let mut node = Node { var, children };

        let mut first = node.children.nodes().next().unwrap();

        // Canonical Form: First child is never complemented.
        let mut flipped = false;
        if first.is_complement() {
            node = node.not();
            first = first.not();
            flipped = true;
        }

        if node.children.nodes().all(|node| node == first) {
            if flipped {
                return first.not();
            } else {
                return first;
            }
        }

        let id = self
            .state
            .node_ids
            .entry(node.clone())
            .or_insert_with(|| NodeId::new(self.shared.nodes.push(node), false));

        if flipped {
            id.not()
        } else {
            *id
        }
    }

    /// Returns a boolean variable representing a marker expression.
    pub(crate) fn terminal(&mut self, expr: MarkerExpression) -> NodeId {
        let (var, children) = match expr {
            MarkerExpression::Version { key, specifier } => (
                Variable::Version(key.clone()),
                RangeMap::from_specifier(key, specifier),
            ),
            MarkerExpression::String {
                key,
                operator: MarkerOperator::In,
                value,
            } => (Variable::In { key, value }, RangeMap::from_bool(true)),
            MarkerExpression::String {
                key,
                operator: MarkerOperator::NotIn,
                value,
            } => (Variable::In { key, value }, RangeMap::from_bool(false)),
            MarkerExpression::String {
                key,
                operator: MarkerOperator::Contains,
                value,
            } => (Variable::Contains { key, value }, RangeMap::from_bool(true)),
            MarkerExpression::String {
                key,
                operator: MarkerOperator::NotContains,
                value,
            } => (
                Variable::Contains { key, value },
                RangeMap::from_bool(false),
            ),
            MarkerExpression::String {
                key,
                operator,
                value,
            } => (
                Variable::String(key),
                RangeMap::from_string(operator, value),
            ),
            MarkerExpression::Extra {
                name,
                operator: ExtraOperator::Equal,
            } => (Variable::Extra(name), RangeMap::from_bool(true)),
            MarkerExpression::Extra {
                name,
                operator: ExtraOperator::NotEqual,
            } => (Variable::Extra(name), RangeMap::from_bool(false)),
        };

        self.create_node(var, children)
    }

    pub(crate) fn or(&mut self, x: NodeId, y: NodeId) -> NodeId {
        self.and(x.not(), y.not()).not()
    }

    pub(crate) fn and(&mut self, xi: NodeId, yi: NodeId) -> NodeId {
        if xi == NodeId::TRUE {
            return yi;
        }

        if yi == NodeId::TRUE {
            return xi;
        }

        if xi == yi {
            return xi;
        }

        if xi == NodeId::FALSE || yi == NodeId::FALSE {
            return NodeId::FALSE;
        }

        // One is complemented but not the other.
        if xi.index() == yi.index() {
            return NodeId::FALSE;
        }

        if let Some(result) = self.state.cache.get(&(xi, yi)) {
            return *result;
        }

        // Perform Shannon Expansion for the higher order variable.
        let (x, y) = (self.shared.node(xi), self.shared.node(yi));
        let (func, children) = if x.var < y.var {
            let children = x.children.map(|node| self.and(node.negate(xi), yi));
            (x.var.clone(), children)
        } else if y.var < x.var {
            let children = y.children.map(|node| self.and(node.negate(yi), xi));
            (y.var.clone(), children)
        } else {
            let children = x
                .children
                .merge(&y.children, |x, y| self.and(x.negate(xi), y.negate(yi)));
            (x.var.clone(), children)
        };

        let node = self.create_node(func, children);
        self.state.cache.insert((xi, yi), node);

        node
    }

    pub(crate) fn restrict(&mut self, i: NodeId, f: &impl Fn(&Variable) -> Option<bool>) -> NodeId {
        if matches!(i, NodeId::TRUE | NodeId::FALSE) {
            return i;
        }

        let node = self.shared.node(i);
        if let RangeMap::Boolean { high, low } = node.children {
            if let Some(value) = f(&node.var) {
                let node = if value { high } else { low };
                return node.negate(i);
            }
        }

        let children = node.children.map(|node| self.restrict(node.negate(i), f));
        self.create_node(node.var.clone(), children)
    }

    pub(crate) fn restrict_versions(
        &mut self,
        i: NodeId,
        f: &impl Fn(&Variable) -> Option<Range<Version>>,
    ) -> NodeId {
        if matches!(i, NodeId::TRUE | NodeId::FALSE) {
            return i;
        }

        let node = self.shared.node(i);
        if let RangeMap::Version { ref map } = node.children {
            if let Some(restricted) = f(&node.var) {
                let mut simplified = Vec::new();
                for (range, node) in map {
                    // Don't perform range splitting to avoid overcomplicating the expression,
                    // simply remove unnecessary ranges.
                    // TODO: does this affect canonicalization? instead we might want a "trivially
                    // true" marker node that we omit from the DNF completely, and perform a full merge
                    // here.
                    if !range.is_disjoint(&restricted) {
                        simplified.push((range.clone(), *node));
                        continue;
                    }

                    match simplified.last_mut() {
                        Some((prev, node)) if *node == NodeId::TRUE => *prev = prev.union(&range),
                        _ => simplified.push((range.clone(), NodeId::TRUE)),
                    };
                }

                return self
                    .create_node(node.var.clone(), RangeMap::Version { map: simplified })
                    .negate(i);
            }
        }

        let children = node
            .children
            .map(|node| self.restrict_versions(node.negate(i), f));
        self.create_node(node.var.clone(), children)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct NodeId(usize);

impl NodeId {
    pub(crate) const FALSE: NodeId = NodeId(0);
    pub(crate) const TRUE: NodeId = NodeId(1);

    const fn new(index: usize, negated: bool) -> NodeId {
        NodeId(((index + 1) << 1) | (negated as usize))
    }

    pub(crate) fn is_false(self) -> bool {
        self == NodeId::FALSE
    }

    pub(crate) fn is_true(self) -> bool {
        self == NodeId::TRUE
    }

    pub(crate) fn not(self) -> NodeId {
        NodeId(self.0 ^ 1)
    }

    pub(crate) fn negate(self, parent: NodeId) -> NodeId {
        if parent.is_complement() {
            self.not()
        } else {
            self
        }
    }

    fn index(self) -> usize {
        (self.0 >> 1) - 1
    }

    fn is_complement(self) -> bool {
        (self.0 & 1) == 1
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub(crate) struct Node {
    pub(crate) var: Variable,
    pub(crate) children: RangeMap,
}

impl Node {
    fn not(self) -> Node {
        Node {
            var: self.var,
            children: self.children.not(),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub(crate) enum RangeMap {
    Version { map: Vec<(Range<Version>, NodeId)> },
    String { map: Vec<(Range<String>, NodeId)> },
    Boolean { high: NodeId, low: NodeId },
}

impl RangeMap {
    fn merge(&self, other: &RangeMap, mut f: impl FnMut(NodeId, NodeId) -> NodeId) -> RangeMap {
        match (self, other) {
            (RangeMap::Version { map }, RangeMap::Version { map: other }) => RangeMap::Version {
                map: RangeMap::merge_maps(map, other, f),
            },
            (RangeMap::String { map }, RangeMap::String { map: other }) => RangeMap::String {
                map: RangeMap::merge_maps(map, other, f),
            },
            (
                RangeMap::Boolean { high, low },
                RangeMap::Boolean {
                    high: high2,
                    low: low2,
                },
            ) => RangeMap::Boolean {
                high: f(*high, *high2),
                low: f(*low, *low2),
            },
            _ => unreachable!(),
        }
    }

    fn merge_maps<T>(
        map: &Vec<(Range<T>, NodeId)>,
        other_map: &Vec<(Range<T>, NodeId)>,
        mut f: impl FnMut(NodeId, NodeId) -> NodeId,
    ) -> Vec<(Range<T>, NodeId)>
    where
        T: Clone + Ord,
    {
        let mut versions = map.clone();
        let mut other_versions = other_map.clone();

        let mut combined: Vec<(Range<T>, NodeId)> = Vec::new();
        loop {
            let first = versions.first();
            let Some((range, node)) = first else {
                break;
            };

            let (other_range, other_node) = other_versions.first().unwrap();

            let intersection = range.intersection(&other_range);

            let node = f(*node, *other_node);
            match combined.last_mut() {
                Some((range, prev)) if *prev == node => {
                    *range = range.union(&intersection);
                }
                _ => {
                    combined.push((intersection.clone(), node));
                }
            };

            let range = range.intersection(&intersection.complement());
            let other_range = other_range.intersection(&intersection.complement());

            if range.is_empty() {
                versions.remove(0);
            } else {
                versions[0].0 = range;
            }

            if other_range.is_empty() {
                other_versions.remove(0);
            } else {
                other_versions[0].0 = other_range;
            }
        }

        combined
    }

    fn map(&self, mut f: impl FnMut(NodeId) -> NodeId) -> RangeMap {
        match self {
            RangeMap::Version { map } => RangeMap::Version {
                map: map
                    .iter()
                    .cloned()
                    .map(|(range, node)| (range, f(node)))
                    .collect(),
            },
            RangeMap::String { map } => RangeMap::String {
                map: map
                    .iter()
                    .cloned()
                    .map(|(range, node)| (range, f(node)))
                    .collect(),
            },
            RangeMap::Boolean { high, low } => RangeMap::Boolean {
                low: f(*low),
                high: f(*high),
            },
        }
    }

    fn from_bool(value: bool) -> RangeMap {
        if value {
            RangeMap::Boolean {
                high: NodeId::TRUE,
                low: NodeId::FALSE,
            }
        } else {
            RangeMap::Boolean {
                high: NodeId::FALSE,
                low: NodeId::TRUE,
            }
        }
    }

    fn from_string(operator: MarkerOperator, value: String) -> RangeMap {
        let range: Range<String> = match operator {
            MarkerOperator::Equal | MarkerOperator::TildeEqual => Range::singleton(value),
            MarkerOperator::NotEqual => Range::singleton(value).complement(),
            MarkerOperator::GreaterThan => Range::strictly_higher_than(value),
            MarkerOperator::GreaterEqual => Range::higher_than(value),
            MarkerOperator::LessThan => Range::strictly_lower_than(value),
            MarkerOperator::LessEqual => Range::lower_than(value),
            _ => unreachable!(),
        };

        RangeMap::String {
            map: RangeMap::from_range(range),
        }
    }

    fn from_specifier(key: MarkerValueVersion, specifier: VersionSpecifier) -> RangeMap {
        let specifier = if key == MarkerValueVersion::PythonVersion {
            PubGrubSpecifier::from_release_specifier(&specifier).unwrap()
        } else {
            PubGrubSpecifier::from_pep440_specifier(&specifier).unwrap()
        };

        RangeMap::Version {
            map: RangeMap::from_range(specifier.into()),
        }
    }

    fn from_range<T>(range: Range<T>) -> Vec<(Range<T>, NodeId)>
    where
        T: Ord + Clone + fmt::Debug,
    {
        let complement = range.complement();

        let mut versions: Vec<(Range<T>, NodeId)> = Vec::new();
        for (start, end) in range.iter() {
            let range = Range::from_range_bounds((start.clone(), end.clone()));
            versions.push((range, NodeId::TRUE));
        }

        for (start, end) in complement.iter() {
            let range = Range::from_range_bounds((start.clone(), end.clone()));
            versions.push((range, NodeId::FALSE));
        }

        // Disjoint set so we don't care about equality.
        versions.sort_by(|(range1, _), (range2, _)| {
            let (start1, _) = range1.bounding_range().unwrap();
            let (start2, _) = range2.bounding_range().unwrap();

            match (start1, start2) {
                (Bound::Unbounded, _) => Ordering::Less,
                (_, Bound::Unbounded) => Ordering::Greater,
                (Bound::Included(version1), Bound::Excluded(version2)) if version1 == version2 => {
                    Ordering::Less
                }
                (Bound::Excluded(version1), Bound::Included(version2)) if version1 == version2 => {
                    Ordering::Greater
                }
                (
                    Bound::Included(version1) | Bound::Excluded(version1),
                    Bound::Included(version2) | Bound::Excluded(version2),
                ) => version1.cmp(version2),
            }
        });

        versions
    }

    fn nodes(&self) -> impl Iterator<Item = NodeId> + '_ {
        match self {
            RangeMap::Version { map } => {
                Either::Left(Either::Left(map.iter().map(|(_, node)| *node)))
            }
            RangeMap::String { map } => {
                Either::Left(Either::Right(map.iter().map(|(_, node)| *node)))
            }
            RangeMap::Boolean { high, low } => Either::Right([*low, *high].into_iter()),
        }
    }

    fn not(self) -> RangeMap {
        match self {
            RangeMap::Version { map } => RangeMap::Version {
                map: map
                    .into_iter()
                    .map(|(range, node)| (range, node.not()))
                    .collect(),
            },
            RangeMap::String { map } => RangeMap::String {
                map: map
                    .into_iter()
                    .map(|(range, node)| (range, node.not()))
                    .collect(),
            },
            RangeMap::Boolean { high, low } => RangeMap::Boolean {
                high: high.not(),
                low: low.not(),
            },
        }
    }
}

impl fmt::Debug for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == NodeId::FALSE {
            return write!(f, "false");
        }

        if *self == NodeId::TRUE {
            return write!(f, "true");
        }

        let node = BDD.shared.node(*self);

        match &node.children {
            RangeMap::Version { map } => {
                for (range, child) in map.iter().take(1) {
                    let child = child.negate(*self);

                    write!(
                        f,
                        "if ({:?} in {:?}) {{\n{:?}\n}}\n",
                        node.var, range, child
                    )?;
                }

                for (range, child) in map.iter().skip(1) {
                    let child = child.negate(*self);

                    write!(
                        f,
                        "else if ({:?} in {:?}) {{\n{:?}\n}}\n",
                        node.var, range, child
                    )?;
                }
            }
            RangeMap::String { map } => {
                for (range, child) in map.iter().take(1) {
                    let child = child.negate(*self);

                    write!(
                        f,
                        "if ({:?} in {:?}) {{\n{:?}\n}}\n",
                        node.var, range, child
                    )?;
                }

                for (range, child) in map.iter().skip(1) {
                    let child = child.negate(*self);

                    write!(
                        f,
                        "else if ({:?} in {:?}) {{\n{:?}\n}}\n",
                        node.var, range, child
                    )?;
                }
            }
            RangeMap::Boolean { high, low } => {
                write!(f, "if ({:?}) {{\n{:?}\n}}\n", node.var, high)?;
                write!(f, "else {{\n{:?}\n}}\n", low)?;
            }
        }

        Ok(())
    }
}

#[derive(PartialOrd, Ord, PartialEq, Eq, Hash, Clone, Debug)]
pub(crate) enum Variable {
    Version(MarkerValueVersion),
    String(MarkerValueString),
    In {
        key: MarkerValueString,
        value: String,
    },
    Contains {
        key: MarkerValueString,
        value: String,
    },
    // Keep extra at the leaves, so when simplifying extra expression we just remove the
    // leaves instead of having to reconstruct the entire tree.
    Extra(ExtraName),
}

#[cfg(test)]
mod tests {
    use crate::{
        marker::bdd::{Interner, NodeId},
        MarkerExpression,
    };

    use super::BDD;

    fn expr(s: &str) -> NodeId {
        BDD.terminal(MarkerExpression::from_str(s).unwrap().unwrap())
    }

    #[test]
    fn basic() {
        let m = &*BDD;

        let a = expr("extra == 'foo'");
        assert!(!a.is_false());

        let b = expr("os_name == 'foo'");
        let c = m.or(a, b);
        assert!(!c.is_false());
        assert!(!m.and(a, b).is_false());

        let d = m.and(a, a.not());
        assert!(d.is_false());

        let e = m.or(d, b);
        assert!(!e.is_false());

        let f = m.or(c, c.not());
        assert!(!f.is_false());
        assert!(f.is_true());

        let a = expr("extra == 'foo'");
        assert!(!a.is_false());

        let b = expr("extra != 'foo'");
        assert!(m.and(a, b).is_false());
        assert!(m.or(a, b).is_true());

        let a = expr("os_name >= 'bar'");
        assert!(!a.is_false());

        let b = expr("os_name < 'bar'");
        assert!(m.and(a, b).is_false());
        assert!(m.or(a, b).is_true());

        let c = expr("os_name <= 'bar'");
        assert!(!m.and(a, c).is_false());
        assert!(m.or(a, c).is_true());
    }

    #[test]
    fn version() {
        let m = &*BDD;

        let a = expr("python_version == '3'");
        let b = expr("python_version != '3'");
        let c = expr("python_version >= '3'");
        let d = expr("python_version <= '3'");

        let e = expr("python_version == '2'");
        let z = expr("python_version == '1'");
        assert!(m.and(e, z).is_false());

        assert_eq!(a.not(), b);
        assert_eq!(a, b.not());

        assert!(m.and(a, b).is_false());
        assert!(m.or(a, b).is_true());

        assert_eq!(m.and(a, c), a);
        assert_eq!(m.and(a, d), a);

        assert_eq!(m.and(c, d), a);

        assert!(!m.and(c, d).is_false());
        assert!(m.or(c, d).is_true());
    }

    #[test]
    fn simplify() {
        let m = &*BDD;
        let x = expr("platform_machine == 'x86_64'");
        let n = expr("platform_machine != 'x86_64'");
        let w = expr("platform_machine == 'Windows'");

        assert_eq!(m.or(m.and(x, w), m.and(n, w)), w);
    }

    #[test]
    #[ignore]
    fn bench() {
        for i in (0..10_000).step_by(25) {
            let m = Interner::default();

            let y: Vec<_> = (0..i)
                .map(|i| expr(&format!("python_version == '{i}'")))
                .collect();

            let x = std::time::Instant::now();
            let mut z = NodeId::TRUE;
            for x in y {
                z = m.or(x, z);
            }
            println!("OR {i} variables took {:?}", x.elapsed());
        }
    }
}
