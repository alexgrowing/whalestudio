import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.PlusConditionToZeroCondition
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

def NaSt : Prop :=
  ∀ (k : Type u) [Field k] (T : Over (Spec (.of k))) [GrpObj T], IsTorus T →
    IsAffineHom T.hom ∧
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k')
      (X : Type u) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X)
      (e : fieldBaseChange k k' T ≅ splitTorus (Spec (.of k')) X), IsMonHom e.hom

def NbSt : Prop :=
  ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [IsAdicComplete (IsLocalRing.maximalIdeal V') V']
    (k'' : Type) [Field k''] [Algebra (IsLocalRing.ResidueField V') k'']
    [FiniteDimensional (IsLocalRing.ResidueField V') k''],
  ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal V'') V'') (_ : Algebra V' V''),
    Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧
    ∃ (_ : IsLocalHom (algebraMap V' V'')) (e : k'' ≃+* IsLocalRing.ResidueField V''),
      e.toRingHom.comp (algebraMap (IsLocalRing.ResidueField V') k'') =
        IsLocalRing.ResidueField.map (algebraMap V' V'')

def NcSt : Prop := SemistableReductionPlus → SemistableReductionPlusSplit

def NdSt : Prop :=
  ∀ (K : Type u) [Field K] (G : Over (Spec (.of K))) [GrpObj G] (E : TorusExt G),
    IsAffineHom E.q.left

def NfSt : Prop :=
  ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    (K' : Type) [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    (A : Over (Spec (CommRingCat.of K'))) [GrpObj A], IsAbelianScheme A →
    ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G],
      IsCommMonObj G → Smooth G.hom → IsSeparated G.hom → QuasiCompact G.hom →
      (∃ e : baseChange V' K' G ≅ A, IsMonHom e.hom) →
      Nonempty (TorusExt (specialFibre V' G)) → IsSemiAbelian G

def SemistableCompleteSplit : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A →
  ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
    (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal V') V')
    (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'),
    Algebra.IsIntegral V V' ∧
    (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧
    ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G),
      IsSemiAbelian G ∧
      (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧
      Nonempty (TorusExtension (specialFibre V' G))

def NcZeroSt : Prop := SemistableReductionZero → SemistableCompleteSplit

end ReciprocityTheory.ChartRestriction.G.Semi
