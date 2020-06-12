//! Module for stuff that are not required either to use in a application or to write
//! janet modules.
use core::cmp::Ordering;


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
        JanetBuildConfig { major, minor, patch, bits }
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
    // use super::*;
    use core::cmp::Ordering;

    #[test]
    fn janet_build_config_ord() {
        use super::JanetBuildConfig as Jbc;
        assert_eq!(Ordering::Equal, Jbc::custom(1, 1, 1, 0).cmp(&Jbc::custom(1, 1, 1, 0)));
        assert_eq!(Ordering::Equal, Jbc::custom(1, 2, 1, 0).cmp(&Jbc::custom(1, 2, 1, 1)));

        assert_eq!(Ordering::Less, Jbc::custom(1, 1, 1, 0).cmp(&Jbc::custom(2, 1, 1, 0)));
        assert_eq!(Ordering::Less, Jbc::custom(1, 1, 1, 0).cmp(&Jbc::custom(1, 2, 1, 0)));
        assert_eq!(Ordering::Less, Jbc::custom(1, 1, 1, 0).cmp(&Jbc::custom(1, 1, 2, 0)));

        assert_eq!(Ordering::Greater, Jbc::custom(2, 1, 1, 0).cmp(&Jbc::custom(1, 1, 1, 0)));
        assert_eq!(Ordering::Greater, Jbc::custom(1, 2, 1, 0).cmp(&Jbc::custom(1, 1, 1, 0)));
        assert_eq!(Ordering::Greater, Jbc::custom(1, 1, 2, 0).cmp(&Jbc::custom(1, 1, 1, 0)));
    }
}
