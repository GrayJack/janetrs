//! Module for stuff that are not required either to use in a application or to write
//! janet modules.
use core::{cmp::Ordering, fmt};

use const_fn::const_fn;
use evil_janet::{
    JANET_CURRENT_CONFIG_BITS, JANET_VERSION_MAJOR, JANET_VERSION_MINOR, JANET_VERSION_PATCH,
};

use crate::types::{Janet, JanetCFunction, JanetKeyword, JanetSymbol, JanetTable};

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
    #[const_fn("1.46")]
    pub const fn is_single_threaded(&self) -> bool {
        match self.bits {
            0 | 1 => false,
            2 | 3 => true,
            _ => false,
        }
    }

    /// Return `true` is Janet nanbox bit is set.
    #[inline]
    #[const_fn("1.46")]
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

/// Checks if the given `args` have the same amount of expected arguments, if the check
/// fails it panics from the Janet side.
#[inline]
pub fn check_fix_arity(args: &[Janet], fix_arity: usize) {
    if args.len() != fix_arity {
        crate::jpanic!("arity mismatch, expected {}, got {}", fix_arity, args.len());
    }
}

/// Check if the given `args` have the expected arguments in the inclusive range, if the
/// check fails it panics from the Janet side.
///
/// If `max` is `None`, it will disable the maximum check, allowing variadic arguments.
#[inline]
pub fn check_range_arity(args: &[Janet], min: usize, max: Option<usize>) {
    let arity = args.len();

    if arity < min {
        crate::jpanic!("arity mismatch, expected at least {}, got {}", min, arity);
    }

    if let Some(max) = max {
        if arity > max {
            crate::jpanic!("arity mismatch, expected at most {}, got {}", max, arity);
        }
    }
}

/// Add a Janet immutable variable in the given environment.
#[inline]
pub fn def(env: &mut JanetTable, name: &str, value: impl Into<Janet>, doc: Option<&str>) {
    let mut def = JanetTable::with_capacity(2);
    def.insert(JanetKeyword::new("value"), value);

    if let Some(doc) = doc {
        def.insert(JanetKeyword::new("doc"), doc);
    }

    env.insert(JanetSymbol::new(name), def);
}

// Add a Janet mutable variable in the given environment.
#[inline]
pub fn var(env: &mut JanetTable, name: &str, value: impl Into<Janet>, doc: Option<&str>) {
    let arr = crate::array![value.into()];
    let mut var = JanetTable::with_capacity(2);
    var.insert(JanetKeyword::new("ref"), arr);

    if let Some(doc) = doc {
        var.insert(JanetKeyword::new("doc"), doc);
    }

    env.insert(JanetSymbol::new(name), var);
}

// Add a C function in the given environment and register it on the VM.
#[inline]
pub fn c_func(
    env: &mut JanetTable, namespace: Option<&str>, fn_name: &str, f: JanetCFunction,
    doc: Option<&str>,
)
{
    if let Some(prefix) = namespace {
        let full_name = format!("{}/{}", prefix.trim(), fn_name.trim());
        let mut cfun = JanetTable::with_capacity(2);

        cfun.insert(JanetKeyword::new("value"), f);

        if let Some(d) = doc {
            cfun.insert(JanetKeyword::new("doc"), d);
        }

        env.insert(JanetSymbol::new(&full_name), cfun);
    } else {
        def(env, fn_name, f, doc)
    }

    let mut null_name = crate::types::JanetBuffer::from(fn_name);
    null_name.push_str("\0");

    // We also have to register it in the VM
    unsafe { evil_janet::janet_register(null_name.as_ptr() as *const i8, f) }
}

/// Just a wrapper for the janet panic function
#[doc(hidden)]
#[inline]
pub fn panic(msg: Janet) -> ! {
    unsafe { evil_janet::janet_panicv(msg.inner) }
    #[allow(clippy::empty_loop)]
    loop {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::cmp::Ordering;

    unsafe extern "C" fn test(_argc: i32, _argv: *mut evil_janet::Janet) -> evil_janet::Janet {
        Janet::nil().into()
    }

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

    #[cfg_attr(any(feature = "amalgation", feature = "link-system"), test)]
    fn define() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;
        let mut env = JanetTable::with_capacity(2);
        def(&mut env, "test1", 10, None);
        def(&mut env, "test2", true, Some("Hey"));

        assert_ne!(None, env.get(JanetSymbol::new("test1")));
        assert_ne!(None, env.get(JanetSymbol::new("test2")));

        Ok(())
    }

    #[cfg_attr(any(feature = "amalgation", feature = "link-system"), test)]
    fn variable() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;
        let mut env = JanetTable::with_capacity(2);
        var(&mut env, "test1", 10, None);
        var(&mut env, "test2", true, Some("Hey"));

        assert_ne!(None, env.get(JanetSymbol::new("test1")));
        assert_ne!(None, env.get(JanetSymbol::new("test2")));

        Ok(())
    }

    #[cfg_attr(any(feature = "amalgation", feature = "link-system"), test)]
    fn c_functions() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;
        let mut env = JanetTable::with_capacity(2);
        c_func(&mut env, None, "test1", Some(test), None);
        c_func(&mut env, Some("prefix"), "test2", Some(test), None);
        assert_ne!(None, env.get(JanetSymbol::new("test1")));
        assert_ne!(None, env.get(JanetSymbol::new("prefix/test2")));

        Ok(())
    }
}
