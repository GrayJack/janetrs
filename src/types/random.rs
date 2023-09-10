use core::{fmt, mem};

use rand_core::{RngCore, SeedableRng};

use crate::{IsJanetAbstract, Janet, JanetAbstract};

/// Type representing the Janet pseudorandom number generator
///
/// It uses `xorwow` variation of `Xorshift random number generator`, but the algorithm
/// used is not set to stone and can be changed in future versions of Janet.
#[derive(Clone)]
#[repr(transparent)]
pub struct JanetRng {
    #[allow(dead_code)]
    raw: evil_janet::JanetRNG,
}

impl fmt::Debug for JanetRng {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            return fmt::Debug::fmt(&self.raw, f);
        }
        f.pad("JanetRng")
    }
}

impl IsJanetAbstract for JanetRng {
    type Get = Self;

    const SIZE: usize = mem::size_of::<Self>();

    #[inline]
    fn type_info() -> &'static evil_janet::JanetAbstractType {
        unsafe { &evil_janet::janet_rng_type }
    }
}

impl From<JanetRng> for JanetAbstract {
    #[inline]
    fn from(value: JanetRng) -> Self {
        Self::new(value)
    }
}

impl From<JanetRng> for Janet {
    #[inline]
    fn from(value: JanetRng) -> Self {
        Self::j_abstract(JanetAbstract::new(value))
    }
}

impl SeedableRng for JanetRng {
    type Seed = alloc::vec::Vec<u8>;

    fn from_seed(mut seed: Self::Seed) -> Self {
        unsafe {
            let rng = evil_janet::janet_default_rng();
            evil_janet::janet_rng_longseed(rng, seed.as_mut_ptr(), seed.len() as i32);

            let rng = *rng;
            Self { raw: rng }
        }
    }

    fn seed_from_u64(state: u64) -> Self {
        unsafe {
            let rng = evil_janet::janet_default_rng();
            evil_janet::janet_rng_seed(rng, state as u32);

            let rng = *rng;
            Self { raw: rng }
        }
    }
}

impl RngCore for JanetRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        unsafe {
            evil_janet::janet_rng_u32(
                // SAFETY: this cast is safe because JanetRng is repr(transparent) over
                // evil_janet::JanetRNG
                self as *mut JanetRng as *mut _,
            )
        }
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.next_u32() as u64
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        rand_core::impls::fill_bytes_via_next(self, dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}


#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    use crate::JanetAbstract;

    use super::*;

    #[test]
    fn it_works() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;
        let mut rng = JanetRng::seed_from_u64(11);
        let test1 = rng.next_u32();
        let test2 = rng.next_u32();

        assert_eq!(3469148811, test1);
        assert_ne!(test1, test2);

        let mut rng = JanetRng::from_seed(alloc::vec![11, 9, 23, 255]);
        let test3 = rng.next_u64();
        let test4 = rng.next_u64();

        assert_eq!(1887761749, test3);
        assert_ne!(test3, test4);

        Ok(())
    }

    #[test]
    fn jabstract() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let rng = JanetRng::seed_from_u64(10);
        let mut jabstract = JanetAbstract::new(rng);

        let rng = jabstract.get_mut::<JanetRng>().unwrap();
        let test1 = rng.next_u32();

        assert_eq!(2254829444, test1);

        Ok(())
    }
}
