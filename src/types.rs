use super::traits::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Maybe<T> {
    Nothing,
    Just(T),
}

pub use Maybe::*;

impl<T> From<Option<T>> for Maybe<T> {
    fn from(x: Option<T>) -> Self {
        match x {
            Some(a) => Just(a),
            None => Nothing,
        }
    }
}

impl<T> Kinded for Maybe<T> {
    type Type = T;
}

impl<T1, T2> Rebind<T1, T2> for Maybe<T1> {
    type Rebound = Maybe<T2>;
}

impl<T> Functor<T> for Maybe<T> {
    fn fmap<R>(self, f: impl Fn(T) -> R) -> <Self as Rebind<T, R>>::Rebound {
        match self {
            Just(a) => Just(f(a)),
            Nothing => Nothing,
        }
    }
}

/// I don't know why I need this, but it seems the only way of convincing Rust
/// of the fact that `Nothing` can be of type `<Maybe<X> as Rebind<X, R>>::New`
pub fn nothing<X, R>() -> <Maybe<X> as Rebind<X, R>>::Rebound {
    Nothing
}

impl<T> Monad<T> for Maybe<T>
where
    T: Copy,
{
    fn pure(v: T) -> Self {
        Just(v)
    }

    fn then<R>(
        self,
        f: impl Fn(T) -> <Maybe<T> as Rebind<T, R>>::Rebound,
    ) -> <Maybe<T> as Rebind<T, R>>::Rebound
    where
        Self: Rebind<T, R>,
    {
        // let n: <Maybe<T> as Rebind<T, R>>::New = Nothing as <Maybe<T>>::blubb;
        match self {
            Nothing => nothing::<T, R>(),
            Just(a) => f(a),
        }
    }
}

#[test]
pub fn test_functor() {
    let a = Just(7);
    let b = a
        .fmap(|n| (n & 1) == 0)
        .fmap(|b| if b { "true" } else { "false" })
        .fmap(|s| s.len());
    let c = Just(42).fmap(|n| n.to_string());
    assert_eq!(b, Just(5));
    assert_eq!(c, Just("42".to_string()))
}

#[test]
pub fn test_monad() {
    assert_eq!(
        Maybe::pure(7).then(|x| Just(x > 8)).fmap(|b| !b),
        Just(true)
    );
}

// use core::option::Option;

impl<T> Kinded for Option<T> {
    type Type = T;
}

impl<R, E> Kinded for Result<R, E> {
    type Type = R;
}

impl<T1, T2> Rebind<T1, T2> for Option<T1> {
    type Rebound = Option<T2>;
}

impl<T1, T2, E> Rebind<T1, T2> for Result<T1, E> {
    type Rebound = Result<T2, E>;
}

impl<T> Functor<T> for Option<T> {
    fn fmap<R>(self, f: impl Fn(T) -> R) -> <Self as Rebind<T, R>>::Rebound {
        self.map(f)
    }
}

impl<T, E> Functor<T> for Result<T, E> {
    fn fmap<R>(self, f: impl Fn(T) -> R) -> <Self as Rebind<T, R>>::Rebound {
        match self {
            Ok(a) => Ok(f(a)),
            Err(e) => Err(e),
        }
    }
}

fn none<X, R>() -> <Option<X> as Rebind<X, R>>::Rebound {
    None
}

impl<T> Monad<T> for Option<T> {
    fn pure(v: T) -> Self {
        Some(v)
    }

    fn then<R>(
        self,
        f: impl Fn(T) -> <Option<T> as Rebind<T, R>>::Rebound,
    ) -> <Option<T> as Rebind<T, R>>::Rebound
    where
        Self: Rebind<T, R>,
    {
        // let n: <Maybe<T> as Rebind<T, R>>::New = Nothing as <Maybe<T>>::blubb;
        match self {
            None => none::<T, R>(),
            Some(a) => f(a),
        }
    }
}

fn err<X, R, E>(e: E) -> <Result<X, E> as Rebind<X, R>>::Rebound {
    Err(e)
}

impl<T, E> Monad<T> for Result<T, E> {
    fn pure(v: T) -> Self {
        Ok(v)
    }
    fn then<R>(
        self,
        f: impl Fn(T) -> <Self as Rebind<T, R>>::Rebound,
    ) -> <Self as Rebind<T, R>>::Rebound
    where
        Self: Rebind<T, R>,
    {
        match self {
            Err(e) => err::<T, R, E>(e),
            Ok(r) => f(r),
        }
    }
}
