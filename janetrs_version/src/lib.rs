use core::{cmp::Ordering, fmt};

use evil_janet::{
    JANET_CURRENT_CONFIG_BITS, JANET_VERSION_MAJOR, JANET_VERSION_MINOR, JANET_VERSION_PATCH,
};

/// Janet configuration in the build.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct JanetBuildConfig {
    version: JanetVersion,
    bits:    u32,
}

impl JanetBuildConfig {
    /// Get the current Janet build version.
    #[inline]
    pub const fn current() -> Self {
        Self {
            version: JanetVersion::current(),
            bits:    JANET_CURRENT_CONFIG_BITS,
        }
    }

    /// Create a custom [`JanetBuildConfig`].
    ///
    /// Mostly used to check if current version match a requirement for your code.
    #[inline]
    pub const fn custom(major: u32, minor: u32, patch: u32, bits: u32) -> Self {
        Self {
            version: JanetVersion::custom(major, minor, patch),
            bits,
        }
    }

    /// Return the version of the Janet.
    #[inline]
    pub const fn version(&self) -> JanetVersion {
        self.version
    }

    /// Return `true` if Janet single threaded bit is set.
    #[inline]
    pub const fn is_single_threaded(&self) -> bool {
        match self.bits {
            0 | 1 => false,
            2 | 3 => true,
            _ => false,
        }
    }

    /// Return `true` is Janet nanbox bit is set.
    #[inline]
    pub const fn is_nanbox(&self) -> bool {
        match self.bits {
            0 | 2 => false,
            1 | 3 => true,
            _ => false,
        }
    }
}

/// Janet version representation.
///
/// It has convenient comparison operators implementations with triples `(u32, u32, u32)`,
/// arrays `[u32; 3]` and [`str`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct JanetVersion {
    major: u32,
    minor: u32,
    patch: u32,
}

impl JanetVersion {
    /// Get the current Janet version.
    #[inline]
    pub const fn current() -> Self {
        Self {
            major: JANET_VERSION_MAJOR,
            minor: JANET_VERSION_MINOR,
            patch: JANET_VERSION_PATCH,
        }
    }

    /// Create a custom [`JanetVersion`] given the version number.
    ///
    /// Mostly used to check if current version match a requirement for your code.
    #[inline]
    pub const fn custom(major: u32, minor: u32, patch: u32) -> Self {
        Self {
            major,
            minor,
            patch,
        }
    }

    /// Return the Janet major version.
    #[inline]
    pub const fn major(&self) -> u32 {
        self.major
    }

    /// Return the Janet minor version.
    #[inline]
    pub const fn minor(&self) -> u32 {
        self.minor
    }

    /// Return the Janet patch version.
    #[inline]
    pub const fn patch(&self) -> u32 {
        self.patch
    }
}

impl fmt::Display for JanetVersion {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(
            &format_args!("Janet {}.{}.{}", self.major, self.minor, self.patch),
            f,
        )
    }
}

impl PartialEq<(u32, u32, u32)> for JanetVersion {
    #[inline]
    fn eq(&self, (major, minor, patch): &(u32, u32, u32)) -> bool {
        self.major.eq(major) && self.minor.eq(minor) && self.patch.eq(patch)
    }
}

impl PartialEq<[u32; 3]> for JanetVersion {
    #[inline]
    fn eq(&self, [major, minor, patch]: &[u32; 3]) -> bool {
        self.major.eq(major) && self.minor.eq(minor) && self.patch.eq(patch)
    }
}

impl PartialEq<&str> for JanetVersion {
    #[cfg_attr(feature = "inline-more", inline)]
    fn eq(&self, other: &&str) -> bool {
        if other.split('.').count() > 3 {
            false
        } else {
            other
                .split('.')
                .map(|s| s.parse::<u32>())
                .take(3)
                .zip([self.major, self.minor, self.patch].iter())
                .map(|(o, s)| o.unwrap_or(u32::MAX).eq(s))
                .all(core::convert::identity)
        }
    }
}

impl PartialOrd for JanetVersion {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<(u32, u32, u32)> for JanetVersion {
    #[cfg_attr(feature = "inline-more", inline)]
    fn partial_cmp(&self, (major, minor, patch): &(u32, u32, u32)) -> Option<Ordering> {
        match self.major.cmp(major) {
            Ordering::Equal => match self.minor.cmp(minor) {
                Ordering::Equal => Some(self.patch.cmp(patch)),
                x => Some(x),
            },
            x => Some(x),
        }
    }
}

impl PartialOrd<[u32; 3]> for JanetVersion {
    #[cfg_attr(feature = "inline-more", inline)]
    fn partial_cmp(&self, [major, minor, patch]: &[u32; 3]) -> Option<Ordering> {
        match self.major.cmp(major) {
            Ordering::Equal => match self.minor.cmp(minor) {
                Ordering::Equal => Some(self.patch.cmp(patch)),
                x => Some(x),
            },
            x => Some(x),
        }
    }
}

impl PartialOrd<&str> for JanetVersion {
    #[cfg_attr(feature = "inline-more", inline)]
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        let [major, minor, patch] = {
            let iter = other.split('.');

            if iter.clone().count() > 3 {
                return None;
            }

            let mut arr = [0; 3];

            for (index, elem) in iter.map(|s| s.parse().ok()).enumerate() {
                arr[index] = elem?;
            }
            arr
        };

        match self.major.cmp(&major) {
            Ordering::Equal => match self.minor.cmp(&minor) {
                Ordering::Equal => Some(self.patch.cmp(&patch)),
                x => Some(x),
            },
            x => Some(x),
        }
    }
}

impl Ord for JanetVersion {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
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

    #[test]
    fn janet_version_ord() {
        assert_eq!(
            Ordering::Equal,
            JanetVersion::custom(1, 1, 1).cmp(&JanetVersion::custom(1, 1, 1))
        );
        assert_eq!(
            Ordering::Equal,
            JanetVersion::custom(1, 2, 1).cmp(&JanetVersion::custom(1, 2, 1))
        );

        assert_eq!(
            Ordering::Less,
            JanetVersion::custom(1, 1, 1).cmp(&JanetVersion::custom(2, 1, 1))
        );
        assert_eq!(
            Ordering::Less,
            JanetVersion::custom(1, 1, 1).cmp(&JanetVersion::custom(1, 2, 1))
        );
        assert_eq!(
            Ordering::Less,
            JanetVersion::custom(1, 1, 1).cmp(&JanetVersion::custom(1, 1, 2))
        );

        assert_eq!(
            Ordering::Greater,
            JanetVersion::custom(2, 1, 1).cmp(&JanetVersion::custom(1, 1, 1))
        );
        assert_eq!(
            Ordering::Greater,
            JanetVersion::custom(1, 2, 1).cmp(&JanetVersion::custom(1, 1, 1))
        );
        assert_eq!(
            Ordering::Greater,
            JanetVersion::custom(1, 1, 2).cmp(&JanetVersion::custom(1, 1, 1))
        );
    }

    #[test]
    fn version_eq_tuple() {
        assert!(JanetVersion::custom(1, 10, 0) == (1, 10, 0));
        assert!(JanetVersion::custom(0, 1, 9) == (0, 1, 9));
    }

    #[test]
    fn version_eq_str() {
        assert!(JanetVersion::custom(1, 10, 0) == "1.10.0");
        assert!(JanetVersion::custom(0, 1, 9) == "0.1.9");
    }

    #[test]
    fn version_ord_tuple() {
        assert_eq!(
            Some(Ordering::Equal),
            JanetVersion::custom(1, 1, 1).partial_cmp(&(1, 1, 1))
        );
        assert_eq!(
            Some(Ordering::Equal),
            JanetVersion::custom(1, 2, 1).partial_cmp(&(1, 2, 1))
        );

        assert_eq!(
            Some(Ordering::Less),
            JanetVersion::custom(1, 1, 1).partial_cmp(&(2, 1, 1))
        );
        assert_eq!(
            Some(Ordering::Less),
            JanetVersion::custom(1, 1, 1).partial_cmp(&(1, 2, 1))
        );
        assert_eq!(
            Some(Ordering::Less),
            JanetVersion::custom(1, 1, 1).partial_cmp(&(1, 1, 2))
        );

        assert_eq!(
            Some(Ordering::Greater),
            JanetVersion::custom(2, 1, 1).partial_cmp(&(1, 1, 1))
        );
        assert_eq!(
            Some(Ordering::Greater),
            JanetVersion::custom(1, 2, 1).partial_cmp(&(1, 1, 1))
        );
        assert_eq!(
            Some(Ordering::Greater),
            JanetVersion::custom(1, 1, 2).partial_cmp(&(1, 1, 1))
        );
    }

    #[test]
    fn version_ord_str() {
        assert_eq!(
            Some(Ordering::Equal),
            JanetVersion::custom(1, 1, 1).partial_cmp(&"1.1.1")
        );
        assert_eq!(
            Some(Ordering::Equal),
            JanetVersion::custom(1, 2, 1).partial_cmp(&"1.2.1")
        );

        assert_eq!(
            Some(Ordering::Less),
            JanetVersion::custom(1, 1, 1).partial_cmp(&"2.1.1")
        );
        assert_eq!(
            Some(Ordering::Less),
            JanetVersion::custom(1, 1, 1).partial_cmp(&"1.2.1")
        );
        assert_eq!(
            Some(Ordering::Less),
            JanetVersion::custom(1, 1, 1).partial_cmp(&"1.1.2")
        );

        assert_eq!(
            Some(Ordering::Greater),
            JanetVersion::custom(2, 1, 1).partial_cmp(&"1.1.1")
        );
        assert_eq!(
            Some(Ordering::Greater),
            JanetVersion::custom(1, 2, 1).partial_cmp(&"1.1.1")
        );
        assert_eq!(
            Some(Ordering::Greater),
            JanetVersion::custom(1, 1, 2).partial_cmp(&"1.1.1")
        );

        assert_eq!(None, JanetVersion::custom(1, 1, 2).partial_cmp(&""));
        assert_eq!(
            None,
            JanetVersion::custom(1, 1, 2).partial_cmp(&"version go brr")
        );
        assert_eq!(None, JanetVersion::custom(1, 1, 2).partial_cmp(&"1.1.1.1"));
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
