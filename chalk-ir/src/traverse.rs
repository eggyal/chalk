//! Traits for traversing bits of IR.

use std::fmt::Debug;
use std::ops::ControlFlow;

use crate::*;

mod binder_impls;
mod boring_impls;

/// Applies the given `Folder` to a value, producing a folded result
/// of type `Self::Result`. The result type is typically the same as
/// the source type, but in some cases we convert from borrowed
/// to owned as well (e.g., the folder for `&T` will fold to a fresh
/// `T`; well, actually `T::Result`).
/// Applies the given `visitor` to a value, producing a visited result
/// of type `Visitor::Result`.
pub trait Traverse<I: Interner>: Debug {
    /// The type of value that will be produced once folding is done.
    /// Typically this is `Self`, unless `Self` contains borrowed
    /// values, in which case owned values are produced (for example,
    /// one can fold over a `&T` value where `T: Fold`, in which case
    /// you get back a `T`, not a `&T`).
    type Result;

    /// Apply the given folder `folder` to `self`; `binders` is the
    /// number of binders that are in scope when beginning the
    /// folder. Typically `binders` starts as 0, but is adjusted when
    /// we encounter `Binders<T>` in the IR or other similar
    /// constructs.
    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>;

    /// Apply the given visitor `visitor` to `self`; `binders` is the
    /// number of binders that are in scope when beginning the
    /// visitor. Typically `binders` starts as 0, but is adjusted when
    /// we encounter `Binders<T>` in the IR or other similar
    /// constructs.
    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B>;
}

/// For types where "fold" invokes a callback on the `Folder`, the
/// `SuperFold` trait captures the recursive behavior that folds all
/// the contents of the type.
/// For types where "visit" invokes a callback on the `visitor`, the
/// `SuperVisit` trait captures the recursive behavior that visits all
/// the contents of the type.
pub trait SuperTraverse<I: Interner>: Traverse<I> {
    /// Recursively folds the value.
    fn super_fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E>;

    /// Recursively visits the type contents.
    fn super_visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B>;
}

/// "Folding" a type invokes the `fold_ty` method on the folder; this
/// usually (in turn) invokes `super_fold_ty` to fold the individual
/// parts.
/// "visiting" a type invokes the `visit_ty` method on the visitor; this
/// usually (in turn) invokes `super_visit_ty` to visit the individual
/// parts.
impl<I: Interner> Traverse<I> for Ty<I> {
    type Result = Ty<I>;

    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        folder.fold_ty(self, outer_binder)
    }

    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visitor.visit_ty(self, outer_binder)
    }
}

/// "Super fold" for a type invokes te more detailed callbacks on the type
/// "Super visit" for a type invokes the more detailed callbacks on the type
impl<I> SuperTraverse<I> for Ty<I>
where
    I: Interner,
{
    fn super_fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Ty<I>, E> {
        let interner = folder.interner();
        Ok(match self.kind(interner) {
            TyKind::BoundVar(bound_var) => {
                if let Some(bound_var1) = bound_var.shifted_out_to(outer_binder) {
                    // This variable was bound outside of the binders
                    // that we have traversed during folding;
                    // therefore, it is free. Let the folder have a
                    // crack at it.
                    folder.fold_free_var_ty(bound_var1, outer_binder)?
                } else {
                    // This variable was bound within the binders that
                    // we folded over, so just return a bound
                    // variable.
                    self
                }
            }
            TyKind::Dyn(clauses) => TyKind::Dyn(clauses.clone().fold_with(folder, outer_binder)?)
                .intern(folder.interner()),
            TyKind::InferenceVar(var, kind) => {
                folder.fold_inference_ty(*var, *kind, outer_binder)?
            }
            TyKind::Placeholder(ui) => folder.fold_free_placeholder_ty(*ui, outer_binder)?,
            TyKind::Alias(proj) => TyKind::Alias(proj.clone().fold_with(folder, outer_binder)?)
                .intern(folder.interner()),
            TyKind::Function(fun) => TyKind::Function(fun.clone().fold_with(folder, outer_binder)?)
                .intern(folder.interner()),
            TyKind::Adt(id, substitution) => TyKind::Adt(
                id.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::AssociatedType(assoc_ty, substitution) => TyKind::AssociatedType(
                assoc_ty.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Scalar(scalar) => {
                TyKind::Scalar(scalar.fold_with(folder, outer_binder)?).intern(folder.interner())
            }
            TyKind::Str => TyKind::Str.intern(folder.interner()),
            TyKind::Tuple(arity, substitution) => TyKind::Tuple(
                *arity,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::OpaqueType(opaque_ty, substitution) => TyKind::OpaqueType(
                opaque_ty.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Slice(substitution) => {
                TyKind::Slice(substitution.clone().fold_with(folder, outer_binder)?)
                    .intern(folder.interner())
            }
            TyKind::FnDef(fn_def, substitution) => TyKind::FnDef(
                fn_def.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Ref(mutability, lifetime, ty) => TyKind::Ref(
                mutability.fold_with(folder, outer_binder)?,
                lifetime.clone().fold_with(folder, outer_binder)?,
                ty.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Raw(mutability, ty) => TyKind::Raw(
                mutability.fold_with(folder, outer_binder)?,
                ty.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Never => TyKind::Never.intern(folder.interner()),
            TyKind::Array(ty, const_) => TyKind::Array(
                ty.clone().fold_with(folder, outer_binder)?,
                const_.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Closure(id, substitution) => TyKind::Closure(
                id.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Generator(id, substitution) => TyKind::Generator(
                id.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::GeneratorWitness(id, substitution) => TyKind::GeneratorWitness(
                id.fold_with(folder, outer_binder)?,
                substitution.clone().fold_with(folder, outer_binder)?,
            )
            .intern(folder.interner()),
            TyKind::Foreign(id) => {
                TyKind::Foreign(id.fold_with(folder, outer_binder)?).intern(folder.interner())
            }
            TyKind::Error => TyKind::Error.intern(folder.interner()),
        })
    }

    fn super_visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();
        match self.kind(interner) {
            TyKind::BoundVar(bound_var) => {
                if bound_var.shifted_out_to(outer_binder).is_some() {
                    visitor.visit_free_var(*bound_var, outer_binder)
                } else {
                    ControlFlow::Continue(())
                }
            }
            TyKind::Dyn(clauses) => clauses.visit_with(visitor, outer_binder),
            TyKind::InferenceVar(var, _) => visitor.visit_inference_var(*var, outer_binder),
            TyKind::Placeholder(ui) => visitor.visit_free_placeholder(*ui, outer_binder),
            TyKind::Alias(proj) => proj.visit_with(visitor, outer_binder),
            TyKind::Function(fun) => fun.visit_with(visitor, outer_binder),
            TyKind::Adt(_id, substitution) => substitution.visit_with(visitor, outer_binder),
            TyKind::AssociatedType(_assoc_ty, substitution) => {
                substitution.visit_with(visitor, outer_binder)
            }
            TyKind::Scalar(scalar) => scalar.visit_with(visitor, outer_binder),
            TyKind::Str => ControlFlow::Continue(()),
            TyKind::Tuple(arity, substitution) => {
                try_break!(arity.visit_with(visitor, outer_binder));
                substitution.visit_with(visitor, outer_binder)
            }
            TyKind::OpaqueType(opaque_ty, substitution) => {
                try_break!(opaque_ty.visit_with(visitor, outer_binder));
                substitution.visit_with(visitor, outer_binder)
            }
            TyKind::Slice(substitution) => substitution.visit_with(visitor, outer_binder),
            TyKind::FnDef(fn_def, substitution) => {
                try_break!(fn_def.visit_with(visitor, outer_binder));
                substitution.visit_with(visitor, outer_binder)
            }
            TyKind::Ref(mutability, lifetime, ty) => {
                try_break!(mutability.visit_with(visitor, outer_binder));
                try_break!(lifetime.visit_with(visitor, outer_binder));
                ty.visit_with(visitor, outer_binder)
            }
            TyKind::Raw(mutability, ty) => {
                try_break!(mutability.visit_with(visitor, outer_binder));
                ty.visit_with(visitor, outer_binder)
            }
            TyKind::Never => ControlFlow::Continue(()),
            TyKind::Array(ty, const_) => {
                try_break!(ty.visit_with(visitor, outer_binder));
                const_.visit_with(visitor, outer_binder)
            }
            TyKind::Closure(id, substitution) => {
                try_break!(id.visit_with(visitor, outer_binder));
                substitution.visit_with(visitor, outer_binder)
            }
            TyKind::Generator(generator, substitution) => {
                try_break!(generator.visit_with(visitor, outer_binder));
                substitution.visit_with(visitor, outer_binder)
            }
            TyKind::GeneratorWitness(witness, substitution) => {
                try_break!(witness.visit_with(visitor, outer_binder));
                substitution.visit_with(visitor, outer_binder)
            }
            TyKind::Foreign(foreign_ty) => foreign_ty.visit_with(visitor, outer_binder),
            TyKind::Error => ControlFlow::Continue(()),
        }
    }
}

/// "Folding" a lifetime invokes the `fold_lifetime` method on the folder; this
/// usually (in turn) invokes `super_fold_lifetime` to fold the individual
/// parts.
impl<I: Interner> Traverse<I> for Lifetime<I> {
    type Result = Lifetime<I>;

    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        folder.fold_lifetime(self, outer_binder)
    }

    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visitor.visit_lifetime(self, outer_binder)
    }
}

impl<I> SuperTraverse<I> for Lifetime<I>
where
    I: Interner,
{
    fn super_fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Lifetime<I>, E> {
        let interner = folder.interner();
        match self.data(interner) {
            LifetimeData::BoundVar(bound_var) => {
                if let Some(bound_var1) = bound_var.shifted_out_to(outer_binder) {
                    // This variable was bound outside of the binders
                    // that we have traversed during folding;
                    // therefore, it is free. Let the folder have a
                    // crack at it.
                    folder.fold_free_var_lifetime(bound_var1, outer_binder)
                } else {
                    // This variable was bound within the binders that
                    // we folded over, so just return a bound
                    // variable.
                    Ok(self)
                }
            }
            LifetimeData::InferenceVar(var) => folder.fold_inference_lifetime(*var, outer_binder),
            LifetimeData::Placeholder(universe) => {
                folder.fold_free_placeholder_lifetime(*universe, outer_binder)
            }
            LifetimeData::Static => Ok(LifetimeData::<I>::Static.intern(folder.interner())),
            LifetimeData::Empty(ui) => Ok(LifetimeData::<I>::Empty(*ui).intern(folder.interner())),
            LifetimeData::Erased => Ok(LifetimeData::<I>::Erased.intern(folder.interner())),
            LifetimeData::Phantom(void, ..) => match *void {},
        }
    }

    fn super_visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();
        match self.data(interner) {
            LifetimeData::BoundVar(bound_var) => {
                if bound_var.shifted_out_to(outer_binder).is_some() {
                    visitor.visit_free_var(*bound_var, outer_binder)
                } else {
                    ControlFlow::Continue(())
                }
            }
            LifetimeData::InferenceVar(var) => visitor.visit_inference_var(*var, outer_binder),
            LifetimeData::Placeholder(universe) => {
                visitor.visit_free_placeholder(*universe, outer_binder)
            }
            LifetimeData::Static | LifetimeData::Empty(_) | LifetimeData::Erased => {
                ControlFlow::Continue(())
            }
            LifetimeData::Phantom(void, ..) => match *void {},
        }
    }
}

/// "Folding" a const invokes the `fold_const` method on the folder; this
/// usually (in turn) invokes `super_fold_const` to fold the individual
/// parts.
impl<I: Interner> Traverse<I> for Const<I> {
    type Result = Const<I>;

    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        folder.fold_const(self, outer_binder)
    }

    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visitor.visit_const(self, outer_binder)
    }
}

impl<I> SuperTraverse<I> for Const<I>
where
    I: Interner,
{
    fn super_fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Const<I>, E> {
        let interner = folder.interner();
        let ConstData { ref ty, ref value } = self.data(interner);
        let mut fold_ty = || ty.clone().fold_with(folder, outer_binder);
        match value {
            ConstValue::BoundVar(bound_var) => {
                if let Some(bound_var1) = bound_var.shifted_out_to(outer_binder) {
                    folder.fold_free_var_const(ty.clone(), bound_var1, outer_binder)
                } else {
                    Ok(self)
                }
            }
            ConstValue::InferenceVar(var) => {
                folder.fold_inference_const(ty.clone(), *var, outer_binder)
            }
            ConstValue::Placeholder(universe) => {
                folder.fold_free_placeholder_const(ty.clone(), *universe, outer_binder)
            }
            ConstValue::Concrete(ev) => Ok(ConstData {
                ty: fold_ty()?,
                value: ConstValue::Concrete(ConcreteConst {
                    interned: ev.interned.clone(),
                }),
            }
            .intern(folder.interner())),
        }
    }

    fn super_visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();
        match &self.data(interner).value {
            ConstValue::BoundVar(bound_var) => {
                if bound_var.shifted_out_to(outer_binder).is_some() {
                    visitor.visit_free_var(*bound_var, outer_binder)
                } else {
                    ControlFlow::Continue(())
                }
            }
            ConstValue::InferenceVar(var) => visitor.visit_inference_var(*var, outer_binder),
            ConstValue::Placeholder(universe) => {
                visitor.visit_free_placeholder(*universe, outer_binder)
            }
            ConstValue::Concrete(_) => ControlFlow::Continue(()),
        }
    }
}

/// Folding a goal invokes the `fold_goal` callback (which will, by
/// default, invoke super-fold).
impl<I: Interner> Traverse<I> for Goal<I> {
    type Result = Goal<I>;

    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        folder.fold_goal(self, outer_binder)
    }

    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visitor.visit_goal(self, outer_binder)
    }
}

/// Superfold folds recursively.
impl<I: Interner> SuperTraverse<I> for Goal<I> {
    fn super_fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        let interner = folder.interner();
        Ok(Goal::new(
            interner,
            self.data(interner)
                .clone()
                .fold_with(folder, outer_binder)?,
        ))
    }

    fn super_visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        let interner = visitor.interner();
        self.data(interner).visit_with(visitor, outer_binder)
    }
}

/// Folding a program clause invokes the `fold_program_clause`
/// callback on the folder (which will, by default, invoke the
/// `super_fold_with` method on the program clause).
impl<I: Interner> Traverse<I> for ProgramClause<I> {
    type Result = ProgramClause<I>;

    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        folder.fold_program_clause(self, outer_binder)
    }

    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visitor.visit_program_clause(self, outer_binder)
    }
}

impl<I: Interner> Traverse<I> for WhereClause<I> {
    type Result = WhereClause<I>;

    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        use WhereClause::*;
        Ok(match self {
            Implemented(vi) => Implemented(vi.fold_with(folder, outer_binder)?),
            AliasEq(vi) => AliasEq(vi.fold_with(folder, outer_binder)?),
            LifetimeOutlives(vi) => LifetimeOutlives(vi.fold_with(folder, outer_binder)?),
            TypeOutlives(vi) => TypeOutlives(vi.fold_with(folder, outer_binder)?),
        })
    }

    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visitor.visit_where_clause(self, outer_binder)
    }
}

impl<I: Interner> Traverse<I> for DomainGoal<I> {
    type Result = DomainGoal<I>;

    fn fold_with<E>(
        self,
        folder: &mut dyn Folder<I, Error = E>,
        outer_binder: DebruijnIndex,
    ) -> Result<Self::Result, E> {
        use DomainGoal::*;
        Ok(match self {
            Holds(vi) => Holds(vi.fold_with(folder, outer_binder)?),
            WellFormed(vi) => WellFormed(vi.fold_with(folder, outer_binder)?),
            FromEnv(vi) => FromEnv(vi.fold_with(folder, outer_binder)?),
            Normalize(vi) => Normalize(vi.fold_with(folder, outer_binder)?),
            IsLocal(vi) => IsLocal(vi.fold_with(folder, outer_binder)?),
            IsUpstream(vi) => IsUpstream(vi.fold_with(folder, outer_binder)?),
            IsFullyVisible(vi) => IsFullyVisible(vi.fold_with(folder, outer_binder)?),
            LocalImplAllowed(vi) => LocalImplAllowed(vi.fold_with(folder, outer_binder)?),
            Compatible => Compatible,
            DownstreamType(vi) => DownstreamType(vi.fold_with(folder, outer_binder)?),
            Reveal => Reveal,
            ObjectSafe(vi) => ObjectSafe(vi.fold_with(folder, outer_binder)?),
        })
    }

    fn visit_with<B>(
        &self,
        visitor: &mut dyn Visitor<I, BreakTy = B>,
        outer_binder: DebruijnIndex,
    ) -> ControlFlow<B> {
        visitor.visit_domain_goal(self, outer_binder)
    }
}
