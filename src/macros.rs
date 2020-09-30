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
/// [`Janet`] or transform to [`Janet`] beforehand.
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetTuple`]: ./types/tuple/struct.JanetTuple.html
#[macro_export]
macro_rules! tuple {
    ($elem: expr; $n: expr) => {$crate::types::JanetTuple::with_default_elem($crate::types::Janet::from($elem), $n)};

    ($($val: expr),* $(,)?) => {{
        const LEN: i32 = $crate::count!($($val),*);
        let tuple = $crate::types::JanetTuple::builder(LEN)
            $(.put($crate::types::Janet::from($val)))*;

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
/// Also note that this macro builds the array converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`] or transform to [`Janet`] beforehand.
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

    ($($val: expr),* $(,)?) => {{
        const LEN: i32 = $crate::count!($($val),*);
        let mut arr = $crate::types::JanetArray::with_capacity(LEN);
        $(arr.push($crate::types::Janet::from($val));)*
        arr
    }};
}

/// Creates a [`JanetStruct`] containing the arguments key-value pairs.
///
/// `structs!` allows [`JanetStruct`]s to be defined with a syntax that have key-value
/// pairs as the items of the struct.
///
/// ```
/// use janetrs::{structs, types::Janet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let st = structs! {
///     1 => "one",
///     true => 1,
/// };
///
/// assert_eq!(st.len(), 2);
/// assert_eq!(st.get(1), Some(&Janet::from("one")));
/// assert_eq!(st.get(true), Some(&Janet::integer(1)));
/// ```
///
/// Note that this macro builds the struct converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`] or transform to [`Janet`] beforehand.
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetStruct`]: ./types/tuple/struct.JanetStruct.html
#[macro_export]
macro_rules! structs {
    ($($key: expr => $value: expr),* $(,)?) => {{
        const LEN: i32 = $crate::count!($($key),*);
        let st = $crate::types::JanetStruct::builder(LEN)
            $(.put($crate::types::Janet::from($key), $crate::types::Janet::from($value)))*;

        st.finalize()
    }};
}

/// Creates a [`JanetTable`] containing the arguments key-value pairs.
///
/// `table!` allows [`JanetTable`]s to be defined with a syntax that have key-value
/// pairs as the items of the struct.
///
/// ```
/// use janetrs::{table, types::Janet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let table = table! {
///     1 => "one",
///     true => 1,
/// };
///
/// assert_eq!(table.len(), 2);
/// assert_eq!(table.get(1), Some(&Janet::from("one")));
/// assert_eq!(table.get(true), Some(&Janet::integer(1)));
/// ```
///
/// Note that this macro builds the struct converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`] or transform to [`Janet`] beforehand.
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetTable`]: ./types/tuple/struct.JanetTable.html
#[macro_export]
macro_rules! table {
    () => ($crate::types::JanetTable::new());

    ($($key: expr => $value: expr),* $(,)?) => {{
        const LEN: i32 = $crate::count!($($key),*);
        let mut table = $crate::types::JanetTable::with_capacity(LEN);
        $(let _ = table.insert($crate::types::Janet::from($key), $crate::types::Janet::from($value));)*

        table
    }};
}

/// A macro to make life easier creating modules for Janet from Rust.
///
/// ## The syntax:
/// `janet_mod!(<Janet Module Name (string literal)>; <{<Janet Function Name ((string
/// literal))>, <function pointer>, <Janet documentation string (string literal)>},
/// ...>);` ¹ Itens inside `<>` means mandatory
/// ² `...` means one or more
///
/// # Examples
/// ```
/// use janetrs::{janet_mod, lowlevel, types::*};
///
/// #[no_mangle]
/// unsafe extern "C" fn rust_hello(argc: i32, _argv: *mut lowlevel::Janet) -> lowlevel::Janet {
///     lowlevel::janet_fixarity(argc, 0);
///     println!("Hello from Rust!");
///
///     Janet::nil().into()
/// }
///
/// #[no_mangle]
/// unsafe extern "C" fn hi(argc: i32, _argv: *mut lowlevel::Janet) -> lowlevel::Janet {
///     lowlevel::janet_fixarity(argc, 0);
///
///     Janet::from("Hi! My name is GrayJack!").into()
/// }
///
/// janet_mod!("rust";
///     {"hello", rust_hello, "(rust/hello)\n\nRust say hello"},
///     {"hi", hi, "(rust/hi)\n\nHi! My name is..."}
/// );
/// ```
#[macro_export]
macro_rules! janet_mod {
    ($mod_name: literal; $({$fn_name: literal, $fn: expr, $fn_doc: literal}),* $(,)?) => {
        #[no_mangle]
        pub unsafe extern "C" fn _janet_mod_config() -> $crate::lowlevel::JanetBuildConfig {
            $crate::lowlevel::JanetBuildConfig {
                major: $crate::lowlevel::JANET_VERSION_MAJOR,
                minor: $crate::lowlevel::JANET_VERSION_MINOR,
                patch: $crate::lowlevel::JANET_VERSION_PATCH,
                bits:  $crate::lowlevel::JANET_CURRENT_CONFIG_BITS,
            }
        }

        #[no_mangle]
        pub unsafe extern "C" fn _janet_init(env: *mut $crate::lowlevel::JanetTable) {
            $crate::lowlevel::janet_cfuns(env, concat!($mod_name, "\0").as_ptr() as *const i8, [
                $(
                    $crate::lowlevel::JanetReg {
                        name: concat!($fn_name, "\0").as_ptr() as *const i8,
                        cfun: Some($fn),
                        documentation: concat!($fn_doc, "\0").as_ptr() as *const i8,
                    },
                )*

                $crate::lowlevel::JanetReg {
                    name: std::ptr::null(),
                    cfun: None,
                    documentation: std::ptr::null(),
                },
            ].as_ptr())
        }
    };
}

/// Causes a panic in the Janet side. Diferently of the Rust `panic!` macro, this macro
/// does **not** terminate the current thread. Instead, it sends a error signal with the
/// passed message where the Janet runtime takes care to properly exit.
///
/// # Examples
/// ```ignore
/// use janetrs::jpanic;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
/// jpanic!();
/// jpanic!("this is a terrible mistake!");
/// jpanic!(4); // In simple cases you can use any type that Janet implements From trait
/// jpanic!("this is a {} {message}", "fancy", message = "message");
/// ```
#[macro_export]
macro_rules! jpanic {
    () => {
        $crate::util::panic($crate::types::Janet::from("explicity panic"));
    };
    ($msg: expr $(,)?) => {
        $crate::util::panic($crate::types::Janet::from($msg));
    };
    ($msg: expr, $($arg:tt)+) => {
        $crate::util::panic($crate::types::Janet::from(format!($msg, $($arg)+).as_str()));
    };
}

/// Execute a [`JanetCFunction`] and catch any janet panic that may happen as a
/// [`Result`].
///
/// # Examples
/// ```ignore
/// use janetrs::{jcatch, jpanic, types::Janet};
///
/// fn panic_fn() {
///     jpanic!("Help!");
/// }
///
/// #[janet_fn]
/// fn test(args: &mut [Janet]) -> Janet {
///     let res = jcatch!(panic_fn());
///     dbg!(res);
///     Janet::nil()
/// }
/// ```
///
/// [`JanetCFunction`]: ./types/struct.JanetCFunction.html
#[macro_export]
macro_rules! jcatch {
    ($e:expr) => {{
        let mut state = $crate::types::function::JanetTryState::init();

        if let Some(signal) = state.signal() {
            if matches!(
                signal,
                $crate::types::JanetSignal::Ok
                    | $crate::types::JanetSignal::Yield
                    | $crate::types::JanetSignal::User9
            ) {
                Ok($e)
            } else {
                Err(state.payload())
            }
        } else {
            Err($crate::types::Janet::from("No fiber to run."))
        }
    }};
}

/// Macro that tries to run a expression, and if it panics in Rust side, it tries to
/// recover from that and pass the Rust panic string to a Janet Panic.
///
/// This uses the [`catch_unwind`] function, and therefore have the same guarantees as it.
///
/// # Examples
/// ```ignore
/// # #![allow(unconditional_panic)]
/// use janetrs::jtry;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let arr = [10; 5];
/// let val_index_2 = jtry!(arr[2]); // Not going to panic
/// let val_index_20 = jtry!(arr[20]); // Index out bounds
/// ```
///
/// [`catch_unwind`]: https://doc.rust-lang.org/std/panic/fn.catch_unwind.html
#[cfg(feature = "std")]
#[macro_export]
macro_rules! jtry {
    ($e:expr) => {{
        ::std::panic::catch_unwind(|| $e).unwrap_or_else(|err| {
            if let Some(err) = err.downcast_ref::<String>() {
                $crate::jpanic!("{}", err);
            } else {
                $crate::jpanic!();
            }
        })
    }};
}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    // use super::*;
    use crate::types::Janet;

    #[cfg(not(feature = "std"))]
    use serial_test::serial;

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
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
    #[cfg_attr(not(feature = "std"), serial)]
    fn tuple1() {
        let _client = crate::client::JanetClient::init().unwrap();

        let t = tuple!["123"; 3];

        assert_eq!(t.len(), 3);
        assert_eq!(t[0], &Janet::from("123"));
        assert_eq!(t[1], &Janet::from("123"));
        assert_eq!(t[2], &Janet::from("123"));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn array0() {
        let _client = crate::client::JanetClient::init().unwrap();

        let arr = array![];
        assert!(arr.is_empty());
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
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
    #[cfg_attr(not(feature = "std"), serial)]
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

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn structs() {
        let _client = crate::client::JanetClient::init().unwrap();

        let st = structs! {
            1 => "one",
            true => 1,
        };

        assert_eq!(st.len(), 2);
        assert_eq!(st.get(1), Some(&Janet::from("one")));
        assert_eq!(st.get(true), Some(&Janet::integer(1)));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn table() {
        let _client = crate::client::JanetClient::init().unwrap();

        let table = table! {};
        assert!(table.is_empty());

        let table = table! {
            1 => "one",
            true => 1,
        };

        assert_eq!(table.len(), 2);
        assert_eq!(table.get(1), Some(&Janet::from("one")));
        assert_eq!(table.get(true), Some(&Janet::integer(1)));
    }

    #[test]
    #[cfg_attr(not(feature = "std"), serial)]
    fn empty() {
        let _client = crate::client::JanetClient::init().unwrap();

        let arr = array![];
        let tup = tuple![];
        let stru = structs! {};
        let tab = table! {};

        assert!(arr.is_empty());
        assert!(tup.is_empty());
        assert!(stru.is_empty());
        assert!(tab.is_empty());
    }
}
