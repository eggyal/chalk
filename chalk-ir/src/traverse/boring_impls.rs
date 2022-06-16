//! This module contains "rote and uninteresting" impls of `Traverse` for
//! various types. In general, we prefer to derive `Traverse`, but
//! sometimes that doesn't work for whatever reason.
//!
//! The more interesting impls of `Traverse` remain in the `traverse` module.

use crate::*;
use std::{marker::PhantomData, sync::Arc};

/// Convenience function to visit all the items in the iterator it.
pub fn visit_iter<'i, T, I, B>(
    it: impl Iterator<Item = T>,
    visitor: &mut dyn Visitor<I, BreakTy = B>,
    outer_binder: DebruijnIndex,
) -> ControlFlow<B>
where
    T: Traverse<I>,
    I: 'i + Interner,
{
    for e in it {
        try_break!(e.visit_with(visitor, outer_binder));
    }
    ControlFlow::Continue(())
}

impl<T: Clone + Traverse<I>, I: Interner> Traverse<I> for &T {
    type Result = T::Result;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        self.clone().fold_with(folder, outer_binder)
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        T::visit_with(self, visitor, outer_binder)
    }
}

impl<T: Clone + Traverse<I>, I: Interner> Traverse<I> for Vec<T> {
    type Result = Vec<T::Result>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        fold::in_place::fallible_map_vec(self, |e| e.fold_with(folder, outer_binder))
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visit_iter(self.iter(), visitor, outer_binder)
    }
}

impl<T: Clone + Traverse<I>, I: Interner> Traverse<I> for &[T] {
    type Result = Vec<T::Result>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        self.iter()
            .cloned()
            .map(|v| v.fold_with(folder, outer_binder))
            .collect()
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visit_iter(self.iter(), visitor, outer_binder)
    }
}

impl<T: Traverse<I>, I: Interner> Traverse<I> for Box<T> {
    type Result = Box<T::Result>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        fold::in_place::fallible_map_box(self, |e| e.fold_with(folder, outer_binder))
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        T::visit_with(self, visitor, outer_binder)
    }
}

impl<T: Clone + Traverse<I>, I: Interner> Traverse<I> for Arc<T> {
    type Result = Arc<T::Result>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        Arc::try_unwrap(self)
            .unwrap_or_else(|arc| (*arc).clone())
            .fold_with(folder, outer_binder)
            .map(Arc::new)
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        T::visit_with(self, visitor, outer_binder)
    }
}

macro_rules! tuple_traverse {
    ($($n:ident),*) => {
        impl<$($n: Traverse<I>,)* I: Interner> Traverse<I> for ($($n,)*) {
            type Result = ($($n::Result,)*);
            fn fold_with<Error>(self, folder: &mut dyn Folder<I, Error = Error>, outer_binder: DebruijnIndex) -> Result<Self::Result, Error>
            {
                #[allow(non_snake_case)]
                let ($($n),*) = self;
                Ok(($($n.fold_with(folder, outer_binder)?,)*))
            }
            fn visit_with<BT>(&self, visitor: &mut dyn Visitor<I, BreakTy = BT>, outer_binder: DebruijnIndex) -> ControlFlow<BT> {
                #[allow(non_snake_case)]
                let &($(ref $n),*) = self;
                $(
                    try_break!($n.visit_with(visitor, outer_binder));
                )*
                ControlFlow::Continue(())
            }
        }
    }
}

tuple_traverse!(A, B);
tuple_traverse!(A, B, C);
tuple_traverse!(A, B, C, D);
tuple_traverse!(A, B, C, D, E);

impl<T: Traverse<I>, I: Interner> Traverse<I> for Option<T> {
    type Result = Option<T::Result>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        match self {
            None => Ok(None),
            Some(e) => Ok(Some(e.fold_with(folder, outer_binder)?)),
        }
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        match self {
            Some(e) => e.visit_with(visitor, outer_binder),
            None => ControlFlow::Continue(()),
        }
    }
}

impl<I: Interner> Traverse<I> for GenericArg<I> {
    type Result = GenericArg<I>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        let interner = folder.interner();

        let data = self
            .data(interner)
            .clone()
            .fold_with(folder, outer_binder)?;
        Ok(GenericArg::new(interner, data))
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();
        self.data(interner).visit_with(visitor, outer_binder)
    }
}

impl<I: Interner> Traverse<I> for Substitution<I> {
    type Result = Substitution<I>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        let interner = folder.interner();

        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        Substitution::from_fallible(interner, folded)
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();
        visit_iter(self.iter(interner), visitor, outer_binder)
    }
}

impl<I: Interner> Traverse<I> for Goals<I> {
    type Result = Goals<I>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        let interner = folder.interner();
        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        Goals::from_fallible(interner, folded)
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();
        visit_iter(self.iter(interner), visitor, outer_binder)
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! const_visit_copy_fold {
    ($t:ty) => {
        impl<I: Interner> $crate::traverse::Traverse<I> for $t {
            type Result = Self;
            fn fold_with<E>(
                self,
                _folder: &mut dyn ($crate::fold::Folder<I, Error = E>),
                _outer_binder: DebruijnIndex,
            ) -> ::std::result::Result<Self::Result, E> {
                Ok(self)
            }
            fn visit_with<B>(
                &self,
                _visitor: &mut dyn ($crate::visit::Visitor<I, BreakTy = B>),
                _outer_binder: DebruijnIndex,
            ) -> ControlFlow<B> {
                ControlFlow::Continue(())
            }
        }
    };
}

const_visit_copy_fold!(bool);
const_visit_copy_fold!(usize);
const_visit_copy_fold!(UniverseIndex);
const_visit_copy_fold!(PlaceholderIndex);
const_visit_copy_fold!(QuantifierKind);
const_visit_copy_fold!(DebruijnIndex);
const_visit_copy_fold!(ClausePriority);
const_visit_copy_fold!(());
const_visit_copy_fold!(Scalar);
const_visit_copy_fold!(UintTy);
const_visit_copy_fold!(IntTy);
const_visit_copy_fold!(FloatTy);
const_visit_copy_fold!(Mutability);
const_visit_copy_fold!(Safety);

#[doc(hidden)]
#[macro_export]
macro_rules! id_traverse {
    ($t:ident) => {
        impl<I: Interner> $crate::traverse::Traverse<I> for $t<I> {
            type Result = $t<I>;
            fn fold_with<E>(
                self,
                _folder: &mut dyn ($crate::fold::Folder<I, Error = E>),
                _outer_binder: DebruijnIndex,
            ) -> ::std::result::Result<Self::Result, E> {
                Ok(self)
            }
            fn visit_with<B>(
                &self,
                _visitor: &mut dyn ($crate::visit::Visitor<I, BreakTy = B>),
                _outer_binder: DebruijnIndex,
            ) -> ControlFlow<B> {
                ControlFlow::Continue(())
            }
        }
    };
}

id_traverse!(ImplId);
id_traverse!(AdtId);
id_traverse!(TraitId);
id_traverse!(OpaqueTyId);
id_traverse!(AssocTypeId);
id_traverse!(FnDefId);
id_traverse!(ClosureId);
id_traverse!(GeneratorId);
id_traverse!(ForeignDefId);

impl<I: Interner> SuperTraverse<I> for ProgramClause<I> {
    fn super_fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> ::std::result::Result<Self::Result, E> {
        let clause = self.data(folder.interner()).clone();
        Ok(clause
            .super_fold_with(folder, outer_binder)?
            .intern(folder.interner()))
    }
    fn super_visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();

        self.data(interner).0.visit_with(visitor, outer_binder)
    }
}

impl<I: Interner> Traverse<I> for ProgramClauses<I> {
    type Result = ProgramClauses<I>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        let interner = folder.interner();
        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        ProgramClauses::from_fallible(interner, folded)
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();

        visit_iter(self.iter(interner), visitor, outer_binder)
    }
}

impl<I: Interner> Traverse<I> for Constraints<I> {
    type Result = Constraints<I>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        let interner = folder.interner();
        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        Constraints::from_fallible(interner, folded)
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();

        visit_iter(self.iter(interner), visitor, outer_binder)
    }
}

impl<I: Interner> Traverse<I> for QuantifiedWhereClauses<I> {
    type Result = QuantifiedWhereClauses<I>;
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        let interner = folder.interner();
        let folded = self
            .iter(interner)
            .cloned()
            .map(|p| p.fold_with(folder, outer_binder));
        QuantifiedWhereClauses::from_fallible(interner, folded)
    }
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();

        visit_iter(self.iter(interner), visitor, outer_binder)
    }
}

impl<I: Interner> Traverse<I> for PhantomData<I> {
    type Result = PhantomData<I>;

    fn fold_with<E>(
        self,
        _folder: &mut dyn Folder<I, Error = E>,
        _outer_binder: DebruijnIndex,
    ) -> ::std::result::Result<Self::Result, E> {
        Ok(PhantomData)
    }
    fn visit_with<B>(
        &self,
        _visitor: &mut dyn Visitor<I, BreakTy = B>,
        _outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        ControlFlow::Continue(())
    }
}

impl<I: Interner> SuperTraverse<I> for ProgramClauseData<I> {
    fn super_fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> ::std::result::Result<Self::Result, E> {
        Ok(ProgramClauseData(self.0.fold_with(folder, outer_binder)?))
    }
    fn super_visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        self.0.visit_with(visitor, outer_binder)
    }
}
