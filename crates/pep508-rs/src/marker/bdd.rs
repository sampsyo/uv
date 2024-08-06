use std::cmp::Ordering;
use std::fmt;
use std::ops::Bound;
use std::sync::Mutex;
use std::sync::MutexGuard;

use itertools::Either;
use pep440_rs::{Version, VersionSpecifier};
use pubgrub::Range;
use rustc_hash::FxHashMap;
use std::sync::LazyLock;
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

pub(crate) static BDD: LazyLock<Interner> = LazyLock::new(Interner::default);

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
            MarkerExpression::Version { key, specifier } => {
                (Variable::Version(key), RangeMap::from_specifier(specifier))
            }
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
            let children = x.children.map(xi, |node| self.and(node, yi));
            (x.var.clone(), children)
        } else if y.var < x.var {
            let children = y.children.map(yi, |node| self.and(node, xi));
            (y.var.clone(), children)
        } else {
            let children = x.children.merge(xi, &y.children, yi, |x, y| self.and(x, y));
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

        let children = node.children.map(i, |node| self.restrict(node, f));
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
            if let Some(allowed) = f(&node.var) {
                let mut simplified = SmallVec::new();
                for (range, node) in map {
                    let restricted = range.intersection(&allowed);
                    if restricted.is_empty() {
                        continue;
                    }

                    // no need to merge as more restricted ranges and already disjoint
                    simplified.push((restricted.clone(), *node));
                }

                return self
                    .create_node(node.var.clone(), RangeMap::Version { map: simplified })
                    .negate(i);
            }
        }

        let children = node.children.map(i, |node| self.restrict_versions(node, f));
        self.create_node(node.var.clone(), children)
    }
}

fn can_merge<T>(range1: &Range<T>, range2: &Range<T>) -> bool
where
    T: Ord + Clone + fmt::Debug,
{
    let Some((_, end)) = range1.bounding_range() else {
        return false;
    };
    let Some((start, _)) = range2.bounding_range() else {
        return false;
    };

    match (end, start) {
        (Bound::Included(v1), Bound::Excluded(v2)) if v1 == v2 => true,
        (Bound::Excluded(v1), Bound::Included(v2)) if v1 == v2 => true,
        _ => false,
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

// Enough two equalities and three complement ranges.
type SmallVec<T> = smallvec::SmallVec<[T; 5]>;

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub(crate) enum RangeMap {
    Version {
        map: SmallVec<(Range<Version>, NodeId)>,
    },
    String {
        map: SmallVec<(Range<String>, NodeId)>,
    },
    Boolean {
        high: NodeId,
        low: NodeId,
    },
}

impl RangeMap {
    fn merge(
        &self,
        parent: NodeId,
        map2: &RangeMap,
        parent2: NodeId,
        mut f: impl FnMut(NodeId, NodeId) -> NodeId,
    ) -> RangeMap {
        match (self, map2) {
            (RangeMap::Version { map }, RangeMap::Version { map: map2 }) => RangeMap::Version {
                map: RangeMap::merge_ranges(map, parent, map2, parent2, f),
            },
            (RangeMap::String { map }, RangeMap::String { map: map2 }) => RangeMap::String {
                map: RangeMap::merge_ranges(map, parent, map2, parent2, f),
            },
            (
                RangeMap::Boolean { high, low },
                RangeMap::Boolean {
                    high: high2,
                    low: low2,
                },
            ) => RangeMap::Boolean {
                high: f(high.negate(parent), high2.negate(parent)),
                low: f(low.negate(parent), low2.negate(parent)),
            },
            _ => unreachable!(),
        }
    }

    fn merge_ranges<T>(
        map: &SmallVec<(Range<T>, NodeId)>,
        parent: NodeId,
        map2: &SmallVec<(Range<T>, NodeId)>,
        parent2: NodeId,
        mut f: impl FnMut(NodeId, NodeId) -> NodeId,
    ) -> SmallVec<(Range<T>, NodeId)>
    where
        T: Clone + Ord + fmt::Debug,
    {
        let mut combined = SmallVec::new();
        for (range, node) in map.iter() {
            for (range2, node2) in map2.iter() {
                let intersection = range2.intersection(&range);
                if intersection.is_empty() {
                    continue;
                }

                let node = f(node.negate(parent), node2.negate(parent2));
                match combined.last_mut() {
                    Some((range, prev)) if *prev == node && can_merge(range, &intersection) => {
                        *range = range.union(&intersection);
                    }
                    _ => combined.push((intersection.clone(), node)),
                }
            }
        }

        combined
    }

    fn map(&self, parent: NodeId, mut f: impl FnMut(NodeId) -> NodeId) -> RangeMap {
        match self {
            RangeMap::Version { map } => RangeMap::Version {
                map: map
                    .iter()
                    .cloned()
                    .map(|(range, node)| (range, f(node.negate(parent))))
                    .collect(),
            },
            RangeMap::String { map } => RangeMap::String {
                map: map
                    .iter()
                    .cloned()
                    .map(|(range, node)| (range, f(node.negate(parent))))
                    .collect(),
            },
            RangeMap::Boolean { high, low } => RangeMap::Boolean {
                low: f(low.negate(parent)),
                high: f(high.negate(parent)),
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
            MarkerOperator::Equal => Range::singleton(value),
            MarkerOperator::NotEqual => Range::singleton(value).complement(),
            MarkerOperator::GreaterThan => Range::strictly_higher_than(value),
            MarkerOperator::GreaterEqual => Range::higher_than(value),
            MarkerOperator::LessThan => Range::strictly_lower_than(value),
            MarkerOperator::LessEqual => Range::lower_than(value),
            MarkerOperator::TildeEqual => unreachable!("string comparisons with ~= are ignored"),
            _ => unreachable!(),
        };

        RangeMap::String {
            map: RangeMap::from_range(range),
        }
    }

    fn from_specifier(specifier: VersionSpecifier) -> RangeMap {
        // The decision diagram relies on the assumption that the negation of a marker tree
        // is the complement of the marker space. However, pre-release versions violate
        // this assumption. For example, the marker `python_version > '3.9' or python_version <= '3.9'`
        // does not match `python_version == 3.9.0a0`. However, it's negation,
        // `python_version > '3.9' and python_version <= '3.9'` also does not include `3.9.0a0`, and is
        // actually `false`.
        //
        // For this reason we ignore pre-release versions completely when evaluating markers.
        let specifier = PubGrubSpecifier::from_release_specifier(&specifier).unwrap();

        RangeMap::Version {
            map: RangeMap::from_range(specifier.into()),
        }
    }

    fn from_range<T>(range: Range<T>) -> SmallVec<(Range<T>, NodeId)>
    where
        T: Ord + Clone + fmt::Debug,
    {
        let complement = range.complement();

        let mut versions = SmallVec::new();
        for (start, end) in range.iter() {
            let range = Range::from_range_bounds((start.clone(), end.clone()));
            versions.push((range, NodeId::TRUE));
        }

        for (start, end) in complement.iter() {
            let range = Range::from_range_bounds((start.clone(), end.clone()));
            versions.push((range, NodeId::FALSE));
        }

        // Disjoint set so we don't care about equality.
        versions.sort_by(|(range1, _), (range2, _)| compare_range_start(range1, range2));

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
            RangeMap::Boolean { high, low } => Either::Right([*high, *low].into_iter()),
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

fn compare_range_start<T>(range1: &Range<T>, range2: &Range<T>) -> Ordering
where
    T: Ord,
{
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
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct NodeId(usize);

impl NodeId {
    pub(crate) const TRUE: NodeId = NodeId(0);
    pub(crate) const FALSE: NodeId = NodeId(1);

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
    use crate::{marker::bdd::NodeId, MarkerExpression};

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
}
