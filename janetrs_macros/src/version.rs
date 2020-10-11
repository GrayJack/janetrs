/// TODO: Cratefy this module since it's just copy-paste of janetrs
use core::{cmp::Ordering, fmt};

/// Janet version representation.
///
/// It has convenient comparison operators implementations with triples `(u32, u32, u32)`,
/// arrays `[u32; 3]` and [`str`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct JanetVersion {
    major: u32,
    minor: u32,
    patch: u32,
}

impl JanetVersion {
    /// Get the current Janet version.
    #[inline]
    pub(crate) const fn current() -> Self {
        Self {
            major: evil_janet::JANET_VERSION_MAJOR,
            minor: evil_janet::JANET_VERSION_MINOR,
            patch: evil_janet::JANET_VERSION_PATCH,
        }
    }

    /// Create a custom [`JanetVersion`] given the version number.
    ///
    /// Mostly used to check if current version match a requirement for your code.
    #[inline]
    pub(crate) const fn custom(major: u32, minor: u32, patch: u32) -> Self {
        Self {
            major,
            minor,
            patch,
        }
    }
}

impl fmt::Display for JanetVersion {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Janet {}.{}.{}", self.major, self.minor, self.patch)
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
        match self.major.cmp(&other.major) {
            Ordering::Equal => match self.minor.cmp(&other.minor) {
                Ordering::Equal => Some(self.patch.cmp(&other.patch)),
                x => Some(x),
            },
            x => Some(x),
        }
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
