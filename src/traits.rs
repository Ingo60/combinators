/// Model higher kinded types, `Type` shall be the type we want to extract, e.g. `u32` in `Option<u32>`
pub trait Kinded {
    type Type;
}

/// A crutch that lets us talk about `F<B>` when we only have `F<A>` under the name `Self`
pub trait Rebind<A, B>: Kinded<Type = A> {
    /// eg. `impl Rebind<A,B> for Foo<A> { type Rebound = Foo<B>; }`
    type Rebound;
}

pub trait Functor<T>
where
    Self: Kinded<Type = T>,
{
    fn fmap<R>(self, f: impl Fn(T) -> R) -> <Self as Rebind<T, R>>::Rebound
    where
        Self: Rebind<T, R>;
}

pub trait Monad<T>: Functor<T>
where
    Self: Kinded<Type = T>,
{
    /// wrap a value in a `Monad`
    fn pure(v: T) -> Self;

    /// > do { x ← self; f x }
    fn then<R>(
        self,
        f: impl Fn(T) -> <Self as Rebind<T, R>>::Rebound,
    ) -> <Self as Rebind<T, R>>::Rebound
    where
        Self: Rebind<T, R>;
}
