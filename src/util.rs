//! Module for stuff that are not required either to use in a application or to write
//! janet modules.
use core::cmp::Ordering;
use core::fmt;


use janet_ll::{
    JANET_CURRENT_CONFIG_BITS, JANET_VERSION_MAJOR, JANET_VERSION_MINOR, JANET_VERSION_PATCH,
};

/// Janet version in this build and configuration bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct JanetBuildConfig {
    major: u32,
    minor: u32,
    patch: u32,
    bits:  u32,
}

impl fmt::Display for JanetBuildConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Janet {}.{}.{}", self.major, self.minor, self.patch)
    }
}

impl JanetBuildConfig {
    /// Get the current Janet build version.
    pub const fn current() -> Self {
        JanetBuildConfig {
            major: JANET_VERSION_MAJOR,
            minor: JANET_VERSION_MINOR,
            patch: JANET_VERSION_PATCH,
            bits:  JANET_CURRENT_CONFIG_BITS,
        }
    }

    /// Create a custom [`JanetBuildConfig`].
    ///
    /// Mostly used to check if current version match a requirement for your code.
    pub const fn custom(major: u32, minor: u32, patch: u32, bits: u32) -> Self {
        JanetBuildConfig {
            major,
            minor,
            patch,
            bits,
        }
    }

    /// Return `true` if Janet single threaded bit is set.
    pub fn is_single_threaded(&self) -> bool {
        match self.bits {
            0 | 1 => false,
            2 | 3 => true,
            _ => unreachable!(),
        }
    }

    /// Return `true` is Janet nanbox bit is set.
    pub fn is_nanbox(&self) -> bool {
        match self.bits {
            0 | 2 => false,
            1 | 3 => true,
            _ => unreachable!(),
        }
    }
}

impl PartialOrd for JanetBuildConfig {
    fn partial_cmp(&self, other: &JanetBuildConfig) -> Option<Ordering> {
        match self.major.cmp(&other.major) {
            Ordering::Equal => match self.minor.cmp(&other.minor) {
                Ordering::Equal => Some(self.patch.cmp(&other.patch)),
                x => Some(x),
            },
            x => Some(x),
        }
    }
}

impl Ord for JanetBuildConfig {
    fn cmp(&self, other: &JanetBuildConfig) -> Ordering {
        match self.major.cmp(&other.major) {
            Ordering::Equal => match self.minor.cmp(&other.minor) {
                Ordering::Equal => self.patch.cmp(&other.patch),
                x => x,
            },
            x => x,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::cmp::Ordering;

    #[test]
    fn janet_build_config_ord() {
        use super::JanetBuildConfig as Jbc;
        assert_eq!(
            Ordering::Equal,
            Jbc::custom(1, 1, 1, 0).cmp(&Jbc::custom(1, 1, 1, 0))
        );
        assert_eq!(
            Ordering::Equal,
            Jbc::custom(1, 2, 1, 0).cmp(&Jbc::custom(1, 2, 1, 1))
        );

        assert_eq!(
            Ordering::Less,
            Jbc::custom(1, 1, 1, 0).cmp(&Jbc::custom(2, 1, 1, 0))
        );
        assert_eq!(
            Ordering::Less,
            Jbc::custom(1, 1, 1, 0).cmp(&Jbc::custom(1, 2, 1, 0))
        );
        assert_eq!(
            Ordering::Less,
            Jbc::custom(1, 1, 1, 0).cmp(&Jbc::custom(1, 1, 2, 0))
        );

        assert_eq!(
            Ordering::Greater,
            Jbc::custom(2, 1, 1, 0).cmp(&Jbc::custom(1, 1, 1, 0))
        );
        assert_eq!(
            Ordering::Greater,
            Jbc::custom(1, 2, 1, 0).cmp(&Jbc::custom(1, 1, 1, 0))
        );
        assert_eq!(
            Ordering::Greater,
            Jbc::custom(1, 1, 2, 0).cmp(&Jbc::custom(1, 1, 1, 0))
        );
    }

    #[test]
    fn config_bits() {
        let test0 = JanetBuildConfig::custom(0, 0, 0, 0);
        let test1 = JanetBuildConfig::custom(0, 0, 0, 1);
        let test2 = JanetBuildConfig::custom(0, 0, 0, 2);
        let test3 = JanetBuildConfig::custom(0, 0, 0, 3);

        assert!(!test0.is_nanbox());
        assert!(!test0.is_single_threaded());

        assert!(test1.is_nanbox());
        assert!(!test1.is_single_threaded());

        assert!(!test2.is_nanbox());
        assert!(test2.is_single_threaded());

        assert!(test3.is_nanbox());
        assert!(test3.is_single_threaded());
    }
}
