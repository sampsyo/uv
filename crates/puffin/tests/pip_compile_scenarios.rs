//! DO NOT EDIT
//!
//! Generated with ./scripts/scenarios/update.py
//! Scenarios from <https://github.com/zanieb/packse/tree/a451c95105db0c2897d0ad1bde0703ba0fc40d3a/scenarios>
//!
#![cfg(all(feature = "python", feature = "pypi"))]

use std::path::PathBuf;
use std::process::Command;

use anyhow::Result;
use assert_fs::fixture::{FileWriteStr, PathChild};
use common::{create_venv, BIN_NAME, INSTA_FILTERS};
#[cfg(unix)]
use fs_err::os::unix::fs::symlink as symlink_file;
#[cfg(windows)]
use fs_err::os::windows::fs::symlink_file;
use insta_cmd::_macro_support::insta;
use insta_cmd::{assert_cmd_snapshot, get_cargo_bin};
use puffin_interpreter::find_requested_python;

mod common;

/// Create a directory with the requested Python binaries available.
pub(crate) fn create_bin_with_executables(
    temp_dir: &assert_fs::TempDir,
    python: Vec<&str>,
) -> Result<PathBuf> {
    let bin = temp_dir.child("bin");
    fs_err::create_dir(&bin)?;
    for request in python {
        let executable = find_requested_python(request)?;
        let name = executable
            .file_name()
            .expect("Discovered executable must have a filename");
        symlink_file(&executable, bin.child(name))?;
    }
    Ok(bin.canonicalize()?)
}

/// requires-incompatible-python-version-compatible-override
///
/// The user requires a package which requires a Python version greater than the
/// current version, but they use an alternative Python version for package
/// resolution.
///
/// ```text
/// 006fed96
/// ├── environment
/// │   └── python3.9
/// ├── root
/// │   └── requires a==1.0.0
/// │       └── satisfied by a-1.0.0
/// └── a
///     └── a-1.0.0
///         └── requires python>=3.10 (incompatible with environment)
/// ```
#[test]
fn requires_incompatible_python_version_compatible_override() -> Result<()> {
    let temp_dir = assert_fs::TempDir::new()?;
    let cache_dir = assert_fs::TempDir::new()?;
    let venv = create_venv(&temp_dir, &cache_dir, "3.9");
    let python_versions = vec![];
    let bin = create_bin_with_executables(&temp_dir, python_versions)?;

    // In addition to the standard filters, swap out package names for more realistic messages
    let mut filters = INSTA_FILTERS.to_vec();
    filters.push((r"a-006fed96", "albatross"));
    filters.push((r"-006fed96", ""));

    let requirements_in = temp_dir.child("requirements.in");
    requirements_in.write_str("a-006fed96==1.0.0")?;

    insta::with_settings!({
        filters => filters
    }, {
        assert_cmd_snapshot!(Command::new(get_cargo_bin(BIN_NAME))
            .arg("pip")
            .arg("compile")
            .arg("requirements.in")
            .arg("--python-version=3.11")
            .arg("--extra-index-url")
            .arg("https://test.pypi.org/simple")
            .arg("--cache-dir")
            .arg(cache_dir.path())
            .env("VIRTUAL_ENV", venv.as_os_str())
            .env("PUFFIN_NO_WRAP", "1")
            .env("PUFFIN_PYTHON_PATH", bin)
            .current_dir(&temp_dir), @r###"
        success: true
        exit_code: 0
        ----- stdout -----
        # This file was autogenerated by Puffin v[VERSION] via the following command:
        #    puffin pip compile requirements.in --python-version=3.11 --extra-index-url https://test.pypi.org/simple --cache-dir [CACHE_DIR]
        albatross==1.0.0

        ----- stderr -----
        warning: The requested Python version 3.11 is not available; 3.9.18 will be used to build dependencies instead.
        Resolved 1 package in [TIME]
        "###);
    });

    Ok(())
}

/// requires-compatible-python-version-incompatible-override
///
/// The user requires a package which requires a compatible Python version, but they
/// request an incompatible Python version for package resolution.
///
/// ```text
/// 8c1b0389
/// ├── environment
/// │   └── python3.11
/// ├── root
/// │   └── requires a==1.0.0
/// │       └── satisfied by a-1.0.0
/// └── a
///     └── a-1.0.0
///         └── requires python>=3.10
/// ```
#[test]
fn requires_compatible_python_version_incompatible_override() -> Result<()> {
    let temp_dir = assert_fs::TempDir::new()?;
    let cache_dir = assert_fs::TempDir::new()?;
    let venv = create_venv(&temp_dir, &cache_dir, "3.11");
    let python_versions = vec![];
    let bin = create_bin_with_executables(&temp_dir, python_versions)?;

    // In addition to the standard filters, swap out package names for more realistic messages
    let mut filters = INSTA_FILTERS.to_vec();
    filters.push((r"a-8c1b0389", "albatross"));
    filters.push((r"-8c1b0389", ""));

    let requirements_in = temp_dir.child("requirements.in");
    requirements_in.write_str("a-8c1b0389==1.0.0")?;

    insta::with_settings!({
        filters => filters
    }, {
        assert_cmd_snapshot!(Command::new(get_cargo_bin(BIN_NAME))
            .arg("pip")
            .arg("compile")
            .arg("requirements.in")
            .arg("--python-version=3.9")
            .arg("--extra-index-url")
            .arg("https://test.pypi.org/simple")
            .arg("--cache-dir")
            .arg(cache_dir.path())
            .env("VIRTUAL_ENV", venv.as_os_str())
            .env("PUFFIN_NO_WRAP", "1")
            .env("PUFFIN_PYTHON_PATH", bin)
            .current_dir(&temp_dir), @r###"
        success: false
        exit_code: 1
        ----- stdout -----

        ----- stderr -----
        warning: The requested Python version 3.9 is not available; 3.11.7 will be used to build dependencies instead.
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Python(
            Target,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "3.9",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Root(
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: None,
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
          × No solution found when resolving dependencies:
          ╰─▶ Because the requested Python version (3.9) does not satisfy Python>=3.10 and albatross==1.0.0 depends on Python>=3.10, we can conclude that albatross==1.0.0 cannot be used.
              And because you require albatross==1.0.0, we can conclude that the requirements are unsatisfiable.
        "###);
    });

    Ok(())
}

/// requires-incompatible-python-version-compatible-override-no-wheels
///
/// The user requires a package which requires a incompatible Python version, but
/// they request a compatible Python version for package resolution. There are only
/// source distributions available for the package.
///
/// ```text
/// b8ee1c03
/// ├── environment
/// │   └── python3.9
/// ├── root
/// │   └── requires a==1.0.0
/// │       └── satisfied by a-1.0.0
/// └── a
///     └── a-1.0.0
///         └── requires python>=3.10 (incompatible with environment)
/// ```
#[test]
fn requires_incompatible_python_version_compatible_override_no_wheels() -> Result<()> {
    let temp_dir = assert_fs::TempDir::new()?;
    let cache_dir = assert_fs::TempDir::new()?;
    let venv = create_venv(&temp_dir, &cache_dir, "3.9");
    let python_versions = vec![];
    let bin = create_bin_with_executables(&temp_dir, python_versions)?;

    // In addition to the standard filters, swap out package names for more realistic messages
    let mut filters = INSTA_FILTERS.to_vec();
    filters.push((r"a-b8ee1c03", "albatross"));
    filters.push((r"-b8ee1c03", ""));

    let requirements_in = temp_dir.child("requirements.in");
    requirements_in.write_str("a-b8ee1c03==1.0.0")?;

    // Since there are no wheels for the package and it is not compatible with the
    // local installation, we cannot build the source distribution to determine its
    // dependencies.
    insta::with_settings!({
        filters => filters
    }, {
        assert_cmd_snapshot!(Command::new(get_cargo_bin(BIN_NAME))
            .arg("pip")
            .arg("compile")
            .arg("requirements.in")
            .arg("--python-version=3.11")
            .arg("--extra-index-url")
            .arg("https://test.pypi.org/simple")
            .arg("--cache-dir")
            .arg(cache_dir.path())
            .env("VIRTUAL_ENV", venv.as_os_str())
            .env("PUFFIN_NO_WRAP", "1")
            .env("PUFFIN_PYTHON_PATH", bin)
            .current_dir(&temp_dir), @r###"
        success: false
        exit_code: 1
        ----- stdout -----

        ----- stderr -----
        warning: The requested Python version 3.11 is not available; 3.9.18 will be used to build dependencies instead.
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Python(
            Installed,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "3.9.18",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Root(
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: None,
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
          × No solution found when resolving dependencies:
          ╰─▶ Because the current Python version (3.9.18) does not satisfy Python>=3.10 and albatross==1.0.0 depends on Python>=3.10, we can conclude that albatross==1.0.0 cannot be used.
              And because you require albatross==1.0.0, we can conclude that the requirements are unsatisfiable.
        "###);
    });

    Ok(())
}

/// requires-incompatible-python-version-compatible-override-no-wheels-available-system
///
/// The user requires a package which requires a incompatible Python version, but
/// they request a compatible Python version for package resolution. There are only
/// source distributions available for the package. The user has a compatible Python
/// version installed elsewhere on their system.
///
/// ```text
/// ae5b2665
/// ├── environment
/// │   ├── python3.11
/// │   └── python3.9 (active)
/// ├── root
/// │   └── requires a==1.0.0
/// │       └── satisfied by a-1.0.0
/// └── a
///     └── a-1.0.0
///         └── requires python>=3.10 (incompatible with environment)
/// ```
#[test]
fn requires_incompatible_python_version_compatible_override_no_wheels_available_system(
) -> Result<()> {
    let temp_dir = assert_fs::TempDir::new()?;
    let cache_dir = assert_fs::TempDir::new()?;
    let venv = create_venv(&temp_dir, &cache_dir, "3.9");
    let python_versions = vec!["3.11"];
    let bin = create_bin_with_executables(&temp_dir, python_versions)?;

    // In addition to the standard filters, swap out package names for more realistic messages
    let mut filters = INSTA_FILTERS.to_vec();
    filters.push((r"a-ae5b2665", "albatross"));
    filters.push((r"-ae5b2665", ""));

    let requirements_in = temp_dir.child("requirements.in");
    requirements_in.write_str("a-ae5b2665==1.0.0")?;

    // Since there is a compatible Python version available on the system, it should be
    // used to build the source distributions.
    insta::with_settings!({
        filters => filters
    }, {
        assert_cmd_snapshot!(Command::new(get_cargo_bin(BIN_NAME))
            .arg("pip")
            .arg("compile")
            .arg("requirements.in")
            .arg("--python-version=3.11")
            .arg("--extra-index-url")
            .arg("https://test.pypi.org/simple")
            .arg("--cache-dir")
            .arg(cache_dir.path())
            .env("VIRTUAL_ENV", venv.as_os_str())
            .env("PUFFIN_NO_WRAP", "1")
            .env("PUFFIN_PYTHON_PATH", bin)
            .current_dir(&temp_dir), @r###"
        success: true
        exit_code: 0
        ----- stdout -----
        # This file was autogenerated by Puffin v[VERSION] via the following command:
        #    puffin pip compile requirements.in --python-version=3.11 --extra-index-url https://test.pypi.org/simple --cache-dir [CACHE_DIR]
        albatross==1.0.0

        ----- stderr -----
        Resolved 1 package in [TIME]
        "###);
    });

    Ok(())
}

/// requires-incompatible-python-version-compatible-override-no-compatible-wheels
///
/// The user requires a package which requires a incompatible Python version, but
/// they request a compatible Python version for package resolution. There is a
/// wheel available for the package, but it does not have a compatible tag.
///
/// ```text
/// c0ea406a
/// ├── environment
/// │   └── python3.9
/// ├── root
/// │   └── requires a==1.0.0
/// │       └── satisfied by a-1.0.0
/// └── a
///     └── a-1.0.0
///         └── requires python>=3.10 (incompatible with environment)
/// ```
#[test]
fn requires_incompatible_python_version_compatible_override_no_compatible_wheels() -> Result<()> {
    let temp_dir = assert_fs::TempDir::new()?;
    let cache_dir = assert_fs::TempDir::new()?;
    let venv = create_venv(&temp_dir, &cache_dir, "3.9");
    let python_versions = vec![];
    let bin = create_bin_with_executables(&temp_dir, python_versions)?;

    // In addition to the standard filters, swap out package names for more realistic messages
    let mut filters = INSTA_FILTERS.to_vec();
    filters.push((r"a-c0ea406a", "albatross"));
    filters.push((r"-c0ea406a", ""));

    let requirements_in = temp_dir.child("requirements.in");
    requirements_in.write_str("a-c0ea406a==1.0.0")?;

    // Since there are no compatible wheels for the package and it is not compatible
    // with the local installation, we cannot build the source distribution to
    // determine its dependencies.
    insta::with_settings!({
        filters => filters
    }, {
        assert_cmd_snapshot!(Command::new(get_cargo_bin(BIN_NAME))
            .arg("pip")
            .arg("compile")
            .arg("requirements.in")
            .arg("--python-version=3.11")
            .arg("--extra-index-url")
            .arg("https://test.pypi.org/simple")
            .arg("--cache-dir")
            .arg(cache_dir.path())
            .env("VIRTUAL_ENV", venv.as_os_str())
            .env("PUFFIN_NO_WRAP", "1")
            .env("PUFFIN_PYTHON_PATH", bin)
            .current_dir(&temp_dir), @r###"
        success: false
        exit_code: 1
        ----- stdout -----

        ----- stderr -----
        warning: The requested Python version 3.11 is not available; 3.9.18 will be used to build dependencies instead.
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Python(
            Installed,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "3.9.18",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Root(
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: None,
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
          × No solution found when resolving dependencies:
          ╰─▶ Because the current Python version (3.9.18) does not satisfy Python>=3.10 and albatross==1.0.0 depends on Python>=3.10, we can conclude that albatross==1.0.0 cannot be used.
              And because you require albatross==1.0.0, we can conclude that the requirements are unsatisfiable.
        "###);
    });

    Ok(())
}

/// requires-incompatible-python-version-compatible-override-other-wheel
///
/// The user requires a package which requires a incompatible Python version, but
/// they request a compatible Python version for package resolution. There are only
/// source distributions available for the compatible version of the package, but
/// there is an incompatible version with a wheel available.
///
/// ```text
/// 08a4e843
/// ├── environment
/// │   └── python3.9
/// ├── root
/// │   └── requires a
/// │       ├── satisfied by a-1.0.0
/// │       └── satisfied by a-2.0.0
/// └── a
///     ├── a-1.0.0
///     │   └── requires python>=3.10 (incompatible with environment)
///     └── a-2.0.0
///         └── requires python>=3.12 (incompatible with environment)
/// ```
#[test]
fn requires_incompatible_python_version_compatible_override_other_wheel() -> Result<()> {
    let temp_dir = assert_fs::TempDir::new()?;
    let cache_dir = assert_fs::TempDir::new()?;
    let venv = create_venv(&temp_dir, &cache_dir, "3.9");
    let python_versions = vec![];
    let bin = create_bin_with_executables(&temp_dir, python_versions)?;

    // In addition to the standard filters, swap out package names for more realistic messages
    let mut filters = INSTA_FILTERS.to_vec();
    filters.push((r"a-08a4e843", "albatross"));
    filters.push((r"-08a4e843", ""));

    let requirements_in = temp_dir.child("requirements.in");
    requirements_in.write_str("a-08a4e843")?;

    // Since there are no wheels for the version of the package compatible with the
    // target and it is not compatible with the local installation, we cannot build the
    // source distribution to determine its dependencies. The other version has wheels
    // available, but is not compatible with the target version and cannot be used.
    insta::with_settings!({
        filters => filters
    }, {
        assert_cmd_snapshot!(Command::new(get_cargo_bin(BIN_NAME))
            .arg("pip")
            .arg("compile")
            .arg("requirements.in")
            .arg("--python-version=3.11")
            .arg("--extra-index-url")
            .arg("https://test.pypi.org/simple")
            .arg("--cache-dir")
            .arg(cache_dir.path())
            .env("VIRTUAL_ENV", venv.as_os_str())
            .env("PUFFIN_NO_WRAP", "1")
            .env("PUFFIN_PYTHON_PATH", bin)
            .current_dir(&temp_dir), @r###"
        success: false
        exit_code: 1
        ----- stdout -----

        ----- stderr -----
        warning: The requested Python version 3.11 is not available; 3.9.18 will be used to build dependencies instead.
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                        "2.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Python(
            Installed,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "3.9.18",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                        "2.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                        "2.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Python(
            Target,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "3.11",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Root(
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: None,
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                        "2.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
          × No solution found when resolving dependencies:
          ╰─▶ Because the current Python version (3.9.18) does not satisfy Python>=3.10 and albatross==1.0.0 depends on Python>=3.10, we can conclude that albatross==1.0.0 cannot be used.
              And because there are no versions of albatross that satisfy any of:
                  albatross<1.0.0
                  albatross>1.0.0,<2.0.0
                  albatross>2.0.0
              we can conclude that albatross<2.0.0 cannot be used. (1)

              Because the requested Python version (3.11) does not satisfy Python>=3.12 and albatross==2.0.0 depends on Python>=3.12, we can conclude that albatross==2.0.0 cannot be used.
              And because we know from (1) that albatross<2.0.0 cannot be used, we can conclude that all versions of albatross cannot be used.
              And because you require albatross, we can conclude that the requirements are unsatisfiable.
        "###);
    });

    Ok(())
}

/// requires-python-patch-version-override-no-patch
///
/// The user requires a package which requires a Python version with a patch version
/// and the user provides a target version without a patch version.
///
/// ```text
/// 2e1edfd6
/// ├── environment
/// │   └── python3.8.18
/// ├── root
/// │   └── requires a==1.0.0
/// │       └── satisfied by a-1.0.0
/// └── a
///     └── a-1.0.0
///         └── requires python>=3.8.4
/// ```
#[test]
fn requires_python_patch_version_override_no_patch() -> Result<()> {
    let temp_dir = assert_fs::TempDir::new()?;
    let cache_dir = assert_fs::TempDir::new()?;
    let venv = create_venv(&temp_dir, &cache_dir, "3.8.18");
    let python_versions = vec![];
    let bin = create_bin_with_executables(&temp_dir, python_versions)?;

    // In addition to the standard filters, swap out package names for more realistic messages
    let mut filters = INSTA_FILTERS.to_vec();
    filters.push((r"a-2e1edfd6", "albatross"));
    filters.push((r"-2e1edfd6", ""));

    let requirements_in = temp_dir.child("requirements.in");
    requirements_in.write_str("a-2e1edfd6==1.0.0")?;

    // Since the resolver is asked to solve with 3.8, the minimum compatible Python
    // requirement is treated as 3.8.0.
    insta::with_settings!({
        filters => filters
    }, {
        assert_cmd_snapshot!(Command::new(get_cargo_bin(BIN_NAME))
            .arg("pip")
            .arg("compile")
            .arg("requirements.in")
            .arg("--python-version=3.8")
            .arg("--extra-index-url")
            .arg("https://test.pypi.org/simple")
            .arg("--cache-dir")
            .arg(cache_dir.path())
            .env("VIRTUAL_ENV", venv.as_os_str())
            .env("PUFFIN_NO_WRAP", "1")
            .env("PUFFIN_PYTHON_PATH", bin)
            .current_dir(&temp_dir), @r###"
        success: false
        exit_code: 1
        ----- stdout -----

        ----- stderr -----
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Python(
            Target,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "3.8",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Root(
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: None,
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
        [crates/puffin-resolver/src/pubgrub/report.rs:323] package = Package(
            PackageName(
                "albatross",
            ),
            None,
            None,
        )
        [crates/puffin-resolver/src/pubgrub/report.rs:323] &versions = Flatten {
            inner: FlattenCompat {
                iter: Fuse {
                    iter: Some(
                        IntoIter {
                            inner: Item {
                                opt: Some(
                                    {
                                        "1.0.0",
                                    },
                                ),
                            },
                        },
                    ),
                },
                frontiter: None,
                backiter: None,
            },
        }
          × No solution found when resolving dependencies:
          ╰─▶ Because the requested Python version (3.8) does not satisfy Python>=3.8.4 and albatross==1.0.0 depends on Python>=3.8.4, we can conclude that albatross==1.0.0 cannot be used.
              And because you require albatross==1.0.0, we can conclude that the requirements are unsatisfiable.
        "###);
    });

    Ok(())
}

/// requires-python-patch-version-override-patch-compatible
///
/// The user requires a package which requires a Python version with a patch version
/// and the user provides a target version with a compatible patch version.
///
/// ```text
/// 844899bd
/// ├── environment
/// │   └── python3.8.18
/// ├── root
/// │   └── requires a==1.0.0
/// │       └── satisfied by a-1.0.0
/// └── a
///     └── a-1.0.0
///         └── requires python>=3.8.0
/// ```
#[test]
fn requires_python_patch_version_override_patch_compatible() -> Result<()> {
    let temp_dir = assert_fs::TempDir::new()?;
    let cache_dir = assert_fs::TempDir::new()?;
    let venv = create_venv(&temp_dir, &cache_dir, "3.8.18");
    let python_versions = vec![];
    let bin = create_bin_with_executables(&temp_dir, python_versions)?;

    // In addition to the standard filters, swap out package names for more realistic messages
    let mut filters = INSTA_FILTERS.to_vec();
    filters.push((r"a-844899bd", "albatross"));
    filters.push((r"-844899bd", ""));

    let requirements_in = temp_dir.child("requirements.in");
    requirements_in.write_str("a-844899bd==1.0.0")?;

    insta::with_settings!({
        filters => filters
    }, {
        assert_cmd_snapshot!(Command::new(get_cargo_bin(BIN_NAME))
            .arg("pip")
            .arg("compile")
            .arg("requirements.in")
            .arg("--python-version=3.8.0")
            .arg("--extra-index-url")
            .arg("https://test.pypi.org/simple")
            .arg("--cache-dir")
            .arg(cache_dir.path())
            .env("VIRTUAL_ENV", venv.as_os_str())
            .env("PUFFIN_NO_WRAP", "1")
            .env("PUFFIN_PYTHON_PATH", bin)
            .current_dir(&temp_dir), @r###"
        success: true
        exit_code: 0
        ----- stdout -----
        # This file was autogenerated by Puffin v[VERSION] via the following command:
        #    puffin pip compile requirements.in --python-version=3.8.0 --extra-index-url https://test.pypi.org/simple --cache-dir [CACHE_DIR]
        albatross==1.0.0

        ----- stderr -----
        warning: The requested Python version 3.8.0 is not available; 3.8.18 will be used to build dependencies instead.
        Resolved 1 package in [TIME]
        "###);
    });

    Ok(())
}
