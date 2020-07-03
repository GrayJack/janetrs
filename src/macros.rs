#[doc(hidden)]
#[macro_export]
macro_rules! count {
    (@subst $($x: tt)*) => (());
    ($($rest: expr),*) => (<[()]>::len(&[$($crate::count!(@subst $rest)),*]) as i32);
}

/// Creates a [`JanetTuple`] containing the arguments.
///
/// `tuple!` allows [`JanetTuple`]s to be defined with the same syntax as Rust array
/// expressions. There are 2 forms of this macro:
///  * Create a [`JanetTuple`] containing a given list of elements
/// ```
/// use janetrs::{tuple, types::Janet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let t = tuple![3, true, "hey"];
///
/// assert_eq!(t[0], &Janet::integer(3));
/// assert_eq!(t[1], &Janet::boolean(true));
/// assert_eq!(t[2], &Janet::from("hey"));
/// ```
///  * Create a [`JanetTuple`] from a given element and size
/// ```
/// use janetrs::{types::Janet, tuple};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let t = tuple!["123"; 3];
///
/// assert_eq!(t[0], &Janet::from("123"));
/// assert_eq!(t[1], &Janet::from("123"));
/// assert_eq!(t[2], &Janet::from("123"));
/// ```
///
/// Note that unlike `vec!` from the Rust standard library, this macro doesn't try to
/// clone the elements passed.
///
/// Also note that this macro builds the tuples converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`].
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetTuple`]: ./types/tuple/struct.JanetTuple.html
#[macro_export]
macro_rules! tuple {
    ($elem: expr; $n: expr) => {$crate::types::JanetTuple::with_default_elem($crate::types::Janet::from($elem), $n)};

    ($($val: expr),+ $(,)?) => {{
        const LEN: i32 = $crate::count!($($val),*);
        let tuple = $crate::types::JanetTuple::builder(LEN)
            $(.put($crate::types::Janet::from($val)))+;

        tuple.finalize()
    }};
}

/// Creates a [`JanetArray`] containing the arguments.
///
/// `tuple!` allows [`JanetArray`]s to be defined with the same syntax as Rust array
/// expressions. There are 2 forms of this macro:
///  * Create a [`JanetArray`] containing a given list of elements
/// ```
/// use janetrs::{array, types::Janet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let arr = array![3, true, "hey"];
///
/// assert_eq!(arr[0], &Janet::integer(3));
/// assert_eq!(arr[1], &Janet::boolean(true));
/// assert_eq!(arr[2], &Janet::from("hey"));
/// ```
///  * Create a [`JanetArray`] from a given element and size
/// ```
/// use janetrs::{types::Janet, array};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let arr = array!["123"; 3];
///
/// assert_eq!(arr[0], &Janet::from("123"));
/// assert_eq!(arr[1], &Janet::from("123"));
/// assert_eq!(arr[2], &Janet::from("123"));
/// ```
///
/// Note that unlike `vec!` from the Rust standard library, this macro doesn't try to
/// clone the elements passed.
///
/// Also note that this macro builds the tuples converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`].
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetArray`]: ./types/tuple/struct.JanetArray.html
#[macro_export]
macro_rules! array {
    () => { $crate::types::JanetArray::new() };

    ($elem: expr; $n: expr) => {{
        let mut arr = $crate::types::JanetArray::with_capacity($n);
        (0..$n).for_each(|_| arr.push($crate::types::Janet::from($elem)));
        arr
    }};

    ($($val: expr),+ $(,)?) => {{
        const LEN: i32 = $crate::count!($($val),*);
        let mut arr = $crate::types::JanetArray::with_capacity(LEN);
        $(arr.push($crate::types::Janet::from($val));)+
        arr
    }};
}

#[cfg(all(test, feature = "amalgation"))]
mod tests {
    // use super::*;
    use crate::types::Janet;
    use serial_test::serial;

    #[test]
    #[serial]
    fn tuple0() {
        let _client = crate::client::JanetClient::init().unwrap();

        let t = tuple![0, 1, 2, 3, true, "hey"];

        assert_eq!(t.len(), 6);
        assert_eq!(t[0], &Janet::integer(0));
        assert_eq!(t[1], &Janet::integer(1));
        assert_eq!(t[2], &Janet::integer(2));
        assert_eq!(t[3], &Janet::integer(3));
        assert_eq!(t[4], &Janet::boolean(true));
        assert_eq!(t[5], &Janet::from("hey"));
    }

    #[test]
    #[serial]
    fn tuple1() {
        let _client = crate::client::JanetClient::init().unwrap();

        let t = tuple!["123"; 3];

        assert_eq!(t.len(), 3);
        assert_eq!(t[0], &Janet::from("123"));
        assert_eq!(t[1], &Janet::from("123"));
        assert_eq!(t[2], &Janet::from("123"));
    }

    #[test]
    #[serial]
    fn array0() {
        let _client = crate::client::JanetClient::init().unwrap();

        let arr = array![];
        assert!(arr.is_empty());
    }

    #[test]
    #[serial]
    fn array1() {
        let _client = crate::client::JanetClient::init().unwrap();

        let arr = array![0; 5];
        assert_eq!(arr.len(), 5);

        assert_eq!(arr[0], &Janet::integer(0));
        assert_eq!(arr[1], &Janet::integer(0));
        assert_eq!(arr[2], &Janet::integer(0));
        assert_eq!(arr[3], &Janet::integer(0));
        assert_eq!(arr[4], &Janet::integer(0));
    }

    #[test]
    #[serial]
    fn array2() {
        let _client = crate::client::JanetClient::init().unwrap();

        let arr = array![0, 10.0, 15.5, true, "abc"];
        assert_eq!(arr.len(), 5);

        assert_eq!(arr[0], &Janet::integer(0));
        assert_eq!(arr[1], &Janet::number(10.0));
        assert_eq!(arr[2], &Janet::number(15.5));
        assert_eq!(arr[3], &Janet::boolean(true));
        assert_eq!(arr[4], &Janet::from("abc"));
    }
}
