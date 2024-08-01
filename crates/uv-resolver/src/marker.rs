#![allow(clippy::enum_glob_use, clippy::single_match_else)]

use pep508_rs::{MarkerTree, MarkerTreeKind, MarkerValueVersion};

use crate::RequiresPythonBound;

/// Returns the minimum Python version that can satisfy the [`MarkerTree`], if it's constrained.
pub(crate) fn requires_python_marker(tree: MarkerTree) -> Option<RequiresPythonBound> {
    fn collect_python_markers(tree: MarkerTree, markers: &mut Vec<RequiresPythonBound>) {
        match tree.kind() {
            MarkerTreeKind::True | MarkerTreeKind::False => return,
            MarkerTreeKind::Version(marker) => match marker.key() {
                MarkerValueVersion::PythonVersion | MarkerValueVersion::PythonFullVersion => {
                    for (range, tree) in marker.children() {
                        if !tree.is_false() {
                            // Extract the lower bound.
                            let (lower, _) = range.iter().next().unwrap();
                            markers.push(RequiresPythonBound::new(lower.clone()));
                        }
                    }
                }
                _ => {
                    for (_, tree) in marker.children() {
                        collect_python_markers(tree, markers);
                    }
                }
            },
            MarkerTreeKind::String(marker) => {
                for (_, tree) in marker.children() {
                    collect_python_markers(tree, markers);
                }
            }
            MarkerTreeKind::In(marker) => {
                for (_, tree) in marker.children() {
                    collect_python_markers(tree, markers);
                }
            }
            MarkerTreeKind::Contains(marker) => {
                for (_, tree) in marker.children() {
                    collect_python_markers(tree, markers);
                }
            }
            MarkerTreeKind::Extra(marker) => {
                for (_, tree) in marker.children() {
                    collect_python_markers(tree, markers);
                }
            }
        }
    }

    let mut markers = Vec::new();
    collect_python_markers(tree, &mut markers);
    markers.into_iter().min()
}

// #[cfg(test)]
// mod tests {
//     use pep508_rs::TracingReporter;
//
//     use super::*;
//
//     #[test]
//     fn simplify() {
//         assert_marker_equal(
//             "python_version == '3.9' or python_version == '3.9'",
//             "python_version == '3.9'",
//         );
//
//         assert_marker_equal(
//             "python_version < '3.17' or python_version < '3.18'",
//             "python_version < '3.18'",
//         );
//
//         assert_marker_equal(
//             "python_version > '3.17' or python_version > '3.18' or python_version > '3.12'",
//             "python_version > '3.12'",
//         );
//
//         // a quirk of how pubgrub works, but this is considered part of normalization
//         assert_marker_equal(
//             "python_version > '3.17.post4' or python_version > '3.18.post4'",
//             "python_version > '3.17'",
//         );
//
//         assert_marker_equal(
//             "python_version < '3.17' and python_version < '3.18'",
//             "python_version < '3.17'",
//         );
//
//         assert_marker_equal(
//             "python_version <= '3.18' and python_version == '3.18'",
//             "python_version == '3.18'",
//         );
//
//         assert_marker_equal(
//             "python_version <= '3.18' or python_version == '3.18'",
//             "python_version <= '3.18'",
//         );
//
//         assert_marker_equal(
//             "python_version <= '3.15' or (python_version <= '3.17' and python_version < '3.16')",
//             "python_version < '3.16'",
//         );
//
//         assert_marker_equal(
//             "(python_version > '3.17' or python_version > '3.16') and python_version > '3.15'",
//             "python_version > '3.16'",
//         );
//
//         assert_marker_equal(
//             "(python_version > '3.17' or python_version > '3.16') and python_version > '3.15' and implementation_version == '1'",
//             "implementation_version == '1' and python_version > '3.16'",
//         );
//
//         assert_marker_equal(
//             "('3.17' < python_version or '3.16' < python_version) and '3.15' < python_version and implementation_version == '1'",
//             "implementation_version == '1' and python_version > '3.16'",
//         );
//
//         assert_marker_equal("extra == 'a' or extra == 'a'", "extra == 'a'");
//         assert_marker_equal(
//             "extra == 'a' and extra == 'a' or extra == 'b'",
//             "extra == 'a' or extra == 'b'",
//         );
//
//         // bogus expressions are retained but still normalized
//         assert_marker_equal(
//             "python_version < '3.17' and '3.18' == python_version",
//             "python_version == '3.18' and python_version < '3.17'",
//         );
//
//         // flatten nested expressions
//         assert_marker_equal(
//             "((extra == 'a' and extra == 'b') and extra == 'c') and extra == 'b'",
//             "extra == 'a' and extra == 'b' and extra == 'c'",
//         );
//
//         assert_marker_equal(
//             "((extra == 'a' or extra == 'b') or extra == 'c') or extra == 'b'",
//             "extra == 'a' or extra == 'b' or extra == 'c'",
//         );
//
//         // complex expressions
//         assert_marker_equal(
//             "extra == 'a' or (extra == 'a' and extra == 'b')",
//             "extra == 'a'",
//         );
//
//         assert_marker_equal(
//             "extra == 'a' and (extra == 'a' or extra == 'b')",
//             "extra == 'a'",
//         );
//
//         assert_marker_equal(
//             "(extra == 'a' and (extra == 'a' or extra == 'b')) or extra == 'd'",
//             "extra == 'a' or extra == 'd'",
//         );
//
//         assert_marker_equal(
//             "((extra == 'a' and extra == 'b') or extra == 'c') or extra == 'b'",
//             "extra == 'b' or extra == 'c'",
//         );
//
//         assert_marker_equal(
//             "((extra == 'a' or extra == 'b') and extra == 'c') and extra == 'b'",
//             "extra == 'b' and extra == 'c'",
//         );
//
//         assert_marker_equal(
//             "((extra == 'a' or extra == 'b') and extra == 'c') or extra == 'b'",
//             "extra == 'b' or (extra == 'a' and extra == 'c')",
//         );
//
//         // post-normalization filtering
//         assert_marker_equal(
//             "(python_version < '3.1' or python_version < '3.2') and (python_version < '3.2' or python_version == '3.3')",
//             "python_version < '3.2'",
//         );
//
//         // normalize out redundant ranges
//         assert_normalizes_out("python_version < '3.12.0rc1' or python_version >= '3.12.0rc1'");
//
//         assert_normalizes_out(
//             "extra == 'a' or (python_version < '3.12.0rc1' or python_version >= '3.12.0rc1')",
//         );
//
//         assert_normalizes_to(
//             "extra == 'a' and (python_version < '3.12.0rc1' or python_version >= '3.12.0rc1')",
//             "extra == 'a'",
//         );
//
//         // normalize `!=` operators
//         assert_normalizes_out("python_version != '3.10' or python_version < '3.12'");
//
//         assert_normalizes_to(
//             "python_version != '3.10' or python_version > '3.12'",
//             "python_version < '3.10' or python_version > '3.10'",
//         );
//
//         assert_normalizes_to(yeah just pointing it out for that one, since boxcar::Vec is lazily allocated
//             "python_version != '3.8' and python_version < '3.10'",
//             "python_version < '3.10' and (python_version < '3.8' or python_version > '3.8')",
//         );
//
//         assert_normalizes_to(
//             "python_version != '3.8' and python_version != '3.9'",
//             "(python_version < '3.8' or python_version > '3.8') and (python_version < '3.9' or python_version > '3.9')",
//         );
//
//         // normalize out redundant expressions
//         assert_normalizes_out("sys_platform == 'win32' or sys_platform != 'win32'");
//
//         assert_normalizes_out("'win32' == sys_platform or sys_platform != 'win32'");
//
//         assert_normalizes_out(
//             "sys_platform == 'win32' or sys_platform == 'win32' or sys_platform != 'win32'",
//         );
//
//         assert_normalizes_to(
//             "sys_platform == 'win32' and sys_platform != 'win32'",
//             "sys_platform == 'win32' and sys_platform != 'win32'",
//         );
//     }
//
//     #[test]
//     fn requires_python() {
//         assert_normalizes_out("python_version >= '3.8'");
//         assert_normalizes_out("python_version >= '3.8' or sys_platform == 'win32'");
//
//         assert_normalizes_to(
//             "python_version >= '3.8' and sys_platform == 'win32'",
//             "sys_platform == 'win32'",
//         );
//
//         assert_normalizes_to("python_version == '3.8'", "python_version == '3.8'");
//
//         assert_normalizes_to("python_version <= '3.10'", "python_version <= '3.10'");
//     }
//
//     #[test]
//     fn extra_disjointness() {
//         assert!(!is_disjoint("extra == 'a'", "python_version == '1'"));
//
//         assert!(!is_disjoint("extra == 'a'", "extra == 'a'"));
//         assert!(!is_disjoint("extra == 'a'", "extra == 'b'"));
//         assert!(!is_disjoint("extra == 'b'", "extra == 'a'"));
//         assert!(!is_disjoint("extra == 'b'", "extra != 'a'"));
//         assert!(!is_disjoint("extra != 'b'", "extra == 'a'"));
//         assert!(is_disjoint("extra != 'b'", "extra == 'b'"));
//         assert!(is_disjoint("extra == 'b'", "extra != 'b'"));
//     }
//
//     #[test]
//     fn arbitrary_disjointness() {
//         assert!(is_disjoint(
//             "python_version == 'Linux'",
//             "python_version == '3.7.1'"
//         ));
//     }
//
//     #[test]
//     fn version_disjointness() {
//         assert!(!is_disjoint(
//             "os_name == 'Linux'",
//             "python_version == '3.7.1'"
//         ));
//
//         test_version_bounds_disjointness("python_version");
//
//         assert!(!is_disjoint(
//             "python_version == '3.7.*'",
//             "python_version == '3.7.1'"
//         ));
//     }
//
//     #[test]
//     fn string_disjointness() {
//         assert!(!is_disjoint(
//             "os_name == 'Linux'",
//             "platform_version == '3.7.1'"
//         ));
//         assert!(!is_disjoint(
//             "implementation_version == '3.7.0'",
//             "python_version == '3.7.1'"
//         ));
//
//         // basic version bounds checking should still work with lexicographical comparisons
//         test_version_bounds_disjointness("platform_version");
//
//         assert!(is_disjoint("os_name == 'Linux'", "os_name == 'OSX'"));
//         assert!(is_disjoint("os_name <= 'Linux'", "os_name == 'OSX'"));
//
//         assert!(!is_disjoint(
//             "os_name in 'OSXLinuxWindows'",
//             "os_name == 'OSX'"
//         ));
//         assert!(!is_disjoint("'OSX' in os_name", "'Linux' in os_name"));
//
//         // complicated `in` intersections are not supported
//         assert!(!is_disjoint("os_name in 'OSX'", "os_name in 'Linux'"));
//         assert!(!is_disjoint(
//             "os_name in 'OSXLinux'",
//             "os_name == 'Windows'"
//         ));
//
//         assert!(is_disjoint(
//             "os_name in 'Windows'",
//             "os_name not in 'Windows'"
//         ));
//         assert!(is_disjoint(
//             "'Windows' in os_name",
//             "'Windows' not in os_name"
//         ));
//
//         assert!(!is_disjoint("'Windows' in os_name", "'Windows' in os_name"));
//         assert!(!is_disjoint("'Linux' in os_name", "os_name not in 'Linux'"));
//         assert!(!is_disjoint("'Linux' not in os_name", "os_name in 'Linux'"));
//     }
//
//     #[test]
//     fn combined_disjointness() {
//         assert!(!is_disjoint(
//             "os_name == 'a' and platform_version == '1'",
//             "os_name == 'a'"
//         ));
//         assert!(!is_disjoint(
//             "os_name == 'a' or platform_version == '1'",
//             "os_name == 'a'"
//         ));
//
//         assert!(is_disjoint(
//             "os_name == 'a' and platform_version == '1'",
//             "os_name == 'a' and platform_version == '2'"
//         ));
//         assert!(is_disjoint(
//             "os_name == 'a' and platform_version == '1'",
//             "'2' == platform_version and os_name == 'a'"
//         ));
//         assert!(!is_disjoint(
//             "os_name == 'a' or platform_version == '1'",
//             "os_name == 'a' or platform_version == '2'"
//         ));
//
//         assert!(is_disjoint(
//             "sys_platform == 'darwin' and implementation_name == 'pypy'",
//             "sys_platform == 'bar' or implementation_name == 'foo'",
//         ));
//         assert!(is_disjoint(
//             "sys_platform == 'bar' or implementation_name == 'foo'",
//             "sys_platform == 'darwin' and implementation_name == 'pypy'",
//         ));
//     }
//
//     #[test]
//     fn is_definitively_empty_set() {
//         assert!(is_empty("'wat' == 'wat'"));
//         assert!(is_empty(
//             "python_version < '3.10' and python_version >= '3.10'"
//         ));
//         assert!(is_empty(
//             "(python_version < '3.10' and python_version >= '3.10') \
//              or (python_version < '3.9' and python_version >= '3.9')",
//         ));
//
//         assert!(!is_empty("python_version < '3.10'"));
//         assert!(!is_empty("python_version < '0'"));
//         assert!(!is_empty(
//             "python_version < '3.10' and python_version >= '3.9'"
//         ));
//         assert!(!is_empty(
//             "python_version < '3.10' or python_version >= '3.11'"
//         ));
//     }
//
//     fn test_version_bounds_disjointness(version: &str) {
//         assert!(!is_disjoint(
//             format!("{version} > '2.7.0'"),
//             format!("{version} == '3.6.0'")
//         ));
//         assert!(!is_disjoint(
//             format!("{version} >= '3.7.0'"),
//             format!("{version} == '3.7.1'")
//         ));
//         assert!(!is_disjoint(
//             format!("{version} >= '3.7.0'"),
//             format!("'3.7.1' == {version}")
//         ));
//
//         assert!(is_disjoint(
//             format!("{version} >= '3.7.1'"),
//             format!("{version} == '3.7.0'")
//         ));
//         assert!(is_disjoint(
//             format!("'3.7.1' <= {version}"),
//             format!("{version} == '3.7.0'")
//         ));
//
//         assert!(is_disjoint(
//             format!("{version} < '3.7.0'"),
//             format!("{version} == '3.7.0'")
//         ));
//         assert!(is_disjoint(
//             format!("'3.7.0' > {version}"),
//             format!("{version} == '3.7.0'")
//         ));
//         assert!(is_disjoint(
//             format!("{version} < '3.7.0'"),
//             format!("{version} == '3.7.1'")
//         ));
//
//         assert!(is_disjoint(
//             format!("{version} == '3.7.0'"),
//             format!("{version} == '3.7.1'")
//         ));
//         assert!(is_disjoint(
//             format!("{version} == '3.7.0'"),
//             format!("{version} != '3.7.0'")
//         ));
//     }
//
//     fn is_empty(tree: &str) -> bool {
//         let tree = MarkerTree::parse_reporter(tree, &mut TracingReporter).unwrap();
//         super::is_definitively_empty_set(&tree)
//     }
//
//     fn is_disjoint(one: impl AsRef<str>, two: impl AsRef<str>) -> bool {
//         let one = MarkerTree::parse_reporter(one.as_ref(), &mut TracingReporter).unwrap();
//         let two = MarkerTree::parse_reporter(two.as_ref(), &mut TracingReporter).unwrap();
//         super::is_disjoint(&one, &two) && super::is_disjoint(&two, &one)
//     }
//
//     fn assert_marker_equal(one: impl AsRef<str>, two: impl AsRef<str>) {
//         let bound = RequiresPythonBound::new(Included(Version::new([3, 8])));
//         let tree1 = MarkerTree::parse_reporter(one.as_ref(), &mut TracingReporter).unwrap();
//         let tree1 = normalize(tree1, Some(&bound)).unwrap();
//         let tree2 = MarkerTree::parse_reporter(two.as_ref(), &mut TracingReporter).unwrap();
//         assert_eq!(
//             tree1.to_string(),
//             tree2.to_string(),
//             "failed to normalize {}",
//             one.as_ref()
//         );
//     }
//
//     fn assert_normalizes_to(before: impl AsRef<str>, after: impl AsRef<str>) {
//         let bound = RequiresPythonBound::new(Included(Version::new([3, 8])));
//         let normalized = MarkerTree::parse_reporter(before.as_ref(), &mut TracingReporter)
//             .unwrap()
//             .clone();
//         let normalized = normalize(normalized, Some(&bound)).unwrap();
//         assert_eq!(normalized.to_string(), after.as_ref());
//     }
//
//     fn assert_normalizes_out(before: impl AsRef<str>) {
//         let bound = RequiresPythonBound::new(Included(Version::new([3, 8])));
//         let normalized = MarkerTree::parse_reporter(before.as_ref(), &mut TracingReporter)
//             .unwrap()
//             .clone();
//         assert!(normalize(normalized, Some(&bound)).is_none());
//     }
// }
