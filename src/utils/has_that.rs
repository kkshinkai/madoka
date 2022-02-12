pub trait HasThat<T> where T: PartialEq {
    fn has_a(&self, x: &T) -> bool {
        self.has_that(|it| it == x)
    }

    fn has_any_of(&self, xs: &[T]) -> bool {
        xs.iter().any(|x| self.has_a(x))
    }

    fn has_that<F>(&self, cond: F) -> bool where F: Fn(&T) -> bool;
}

impl<T> HasThat<T> for Option<T> where T: PartialEq {
    fn has_a(&self, x: &T) -> bool {
        match self {
            Some(y) => y == x,
            None => false,
        }
    }

    fn has_any_of(&self, xs: &[T]) -> bool {
        xs.iter().any(|x| self.has_a(x))
    }

    fn has_that<F>(&self, cond: F) -> bool
        where F: Fn(&T) -> bool
    {
        matches!(self, Some(x) if cond(x))
    }
}

impl<T, E> HasThat<T> for Result<T, E> where T: PartialEq {
    fn has_a(&self, x: &T) -> bool where T: PartialEq {
        match self {
            Ok(y) => y == x,
            Err(_) => false,
        }
    }

    fn has_any_of(&self, xs: &[T]) -> bool where T: PartialEq {
        xs.iter().any(|x| self.has_a(x))
    }

    fn has_that<F>(&self, cond: F) -> bool
        where F: Fn(&T) -> bool
    {
        matches!(self, Ok(x) if cond(x))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_contains() {
        assert!(Some(1).has_a(&1));
        assert!(!Some(1).has_a(&2));
        assert!(!None.has_a(&1));

        assert!(Some(1).has_any_of(&[1, 2, 3]));
        assert!(!Some(4).has_any_of(&[1, 2, 3]));
        assert!(!None.has_any_of(&[1, 2, 3]));

        assert!(Some(1).has_that(|x| x == &1));
        assert!(!Some(4).has_that(|x| x == &1));
    }

    #[test]
    fn test_result_contains() {
        assert!(Ok::<_, ()>(1).has_a(&1));
        assert!(!Ok::<_, ()>(1).has_a(&2));
        assert!(!Err(()).has_a(&1));

        assert!(Ok::<_, ()>(1).has_any_of(&[1, 2, 3]));
        assert!(!Ok::<_, ()>(4).has_any_of(&[1, 2, 3]));
        assert!(!Err(()).has_any_of(&[1, 2, 3]));

        assert!(Ok::<_, ()>(1).has_that(|x| x == &1));
        assert!(!Ok::<_, ()>(4).has_that(|x| x == &1));
    }
}
