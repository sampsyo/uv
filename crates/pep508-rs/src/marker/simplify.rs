use std::{fmt, ops::Bound};

use indexmap::IndexMap;
use itertools::Itertools;
use pep440_rs::VersionSpecifier;
use pubgrub::Range;
use rustc_hash::FxBuildHasher;

use crate::{ExtraOperator, MarkerExpression, MarkerOperator, MarkerTree, MarkerTreeKind};

pub(crate) struct Node<T> {
    range: Range<T>,
    implied: bool,
}

pub(crate) fn collect_dnf(
    tree: &MarkerTree,
    dnf: &mut Vec<Vec<MarkerExpression>>,
    path: &mut Vec<MarkerExpression>,
) {
    match tree.kind() {
        MarkerTreeKind::False => return,
        MarkerTreeKind::True => {
            if !path.is_empty() {
                dnf.push(path.clone())
            }
        }
        MarkerTreeKind::Version(marker) => {
            let paths = collect_paths(marker.children());
            for (tree, node) in paths {
                if node.implied {
                    collect_dnf(&tree, dnf, path);
                    continue;
                }

                if let Some(excluded) = range_inequality(&node.range) {
                    let current = path.len();
                    for version in excluded {
                        path.push(MarkerExpression::Version {
                            key: marker.key().clone(),
                            specifier: VersionSpecifier::not_equals_version(version.clone()),
                        });
                    }

                    collect_dnf(&tree, dnf, path);
                    path.truncate(current);
                    continue;
                }

                for bounds in node.range.iter() {
                    let current = path.len();
                    for specifier in VersionSpecifier::from_bounds(bounds) {
                        path.push(MarkerExpression::Version {
                            key: marker.key().clone(),
                            specifier,
                        });
                    }

                    collect_dnf(&tree, dnf, path);
                    path.truncate(current);
                }
            }
        }
        MarkerTreeKind::String(marker) => {
            let paths = collect_paths(marker.children());
            for (tree, node) in paths {
                if node.implied {
                    collect_dnf(&tree, dnf, path);
                    continue;
                }

                if let Some(excluded) = range_inequality(&node.range) {
                    let current = path.len();
                    for value in excluded {
                        path.push(MarkerExpression::String {
                            key: marker.key().clone(),
                            operator: MarkerOperator::NotEqual,
                            value: value.clone(),
                        });
                    }

                    collect_dnf(&tree, dnf, path);
                    path.truncate(current);
                    continue;
                }

                for bounds in node.range.iter() {
                    let current = path.len();
                    for (operator, value) in MarkerOperator::from_bounds(bounds) {
                        path.push(MarkerExpression::String {
                            key: marker.key().clone(),
                            operator,
                            value: value.clone(),
                        });
                    }

                    collect_dnf(&tree, dnf, path);
                    path.truncate(current);
                }
            }
        }
        MarkerTreeKind::In(marker) => {
            for (value, tree) in marker.children() {
                let operator = if value {
                    MarkerOperator::In
                } else {
                    MarkerOperator::NotIn
                };

                let expr = MarkerExpression::String {
                    key: marker.key().clone(),
                    value: marker.value().to_owned(),
                    operator,
                };

                path.push(expr);
                collect_dnf(&tree, dnf, path);
                path.pop();
            }
        }
        MarkerTreeKind::Contains(marker) => {
            for (value, tree) in marker.children() {
                let operator = if value {
                    MarkerOperator::Contains
                } else {
                    MarkerOperator::NotContains
                };

                let expr = MarkerExpression::String {
                    key: marker.key().clone(),
                    value: marker.value().to_owned(),
                    operator,
                };

                path.push(expr);
                collect_dnf(&tree, dnf, path);
                path.pop();
            }
        }
        MarkerTreeKind::Extra(marker) => {
            for (value, tree) in marker.children() {
                let operator = if value {
                    ExtraOperator::Equal
                } else {
                    ExtraOperator::NotEqual
                };

                let expr = MarkerExpression::Extra {
                    name: marker.name().clone(),
                    operator,
                };

                path.push(expr);
                collect_dnf(&tree, dnf, path);
                path.pop();
            }
        }
    }
}

fn collect_paths<'a, T>(
    map: impl Iterator<Item = (&'a Range<T>, MarkerTree)>,
) -> IndexMap<MarkerTree, Node<T>, FxBuildHasher>
where
    T: Ord + Clone + 'a,
{
    let mut paths: IndexMap<_, Node<_>, FxBuildHasher> = IndexMap::default();
    for (range, tree) in map {
        paths
            .entry(tree)
            .and_modify(|node| node.range = node.range.union(range))
            .or_insert_with(|| Node {
                range: range.clone(),
                implied: false,
            });
    }

    if let Some(((tree1, node1), (tree2, node2))) = paths.iter_mut().collect_tuple() {
        if !tree1.is_false() && !tree2.is_false() {
            // If an expression is already implied we can omit it's complement in
            // subsequent expressions.
            //
            // e.g. `foo or (not foo and bar)` is equivalent to `foo or bar` because
            // `foo and bar => foo`.
            if tree1.implies(tree2) {
                node1.implied = true;
            } else if tree2.implies(tree1) {
                node2.implied = true;
            }
        }
    }

    paths
}

fn range_inequality<T>(range: &Range<T>) -> Option<Vec<&T>>
where
    T: Ord + Clone + fmt::Debug,
{
    if range.is_empty() || range.bounding_range() != Some((Bound::Unbounded, Bound::Unbounded)) {
        return None;
    }

    let mut excluded = Vec::new();
    for ((_, end), (start, _)) in range.iter().tuple_windows() {
        match (end, start) {
            (Bound::Excluded(v1), Bound::Excluded(v2)) if v1 == v2 => excluded.push(v1),
            _ => return None,
        }
    }

    Some(excluded)
}
