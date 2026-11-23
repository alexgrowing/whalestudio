import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Semi

def SemistableReductionZero : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A →
  ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
    (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
    (_ : Algebra V V') (_ : Algebra V' K') (_ : IsFractionRing V' K'),
    Module.Finite V V' ∧ Function.Injective (algebraMap V V') ∧
    (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) ∧
    ∃ (G : Over (Spec (CommRingCat.of V'))) (_ : GrpObj G),
      IsCommMonObj G ∧ Smooth G.hom ∧ IsSeparated G.hom ∧ QuasiCompact G.hom ∧
      (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) ∧
      Nonempty (TorusExt (specialFibre V' G))

theorem SemistableReductionPlus.plusCondition_to_zeroCondition (h : SemistableReductionPlus) : SemistableReductionZero := by
  intro V _ _ _ _ K _ _ _ _ A _ hA
  obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, h1, h2, h3, G, i10,
    h4, h5, h6, h7, h8, h9, -⟩ := h V K A hA
  exact ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, h1, h2, h3, G, i10,
    h4, h5, h6, h7, h8, h9⟩

end ReciprocityTheory.ChartRestriction.G.Semi
