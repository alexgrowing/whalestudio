import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotSt
import Lemmata.MiscLemmasJ.Imports

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open Module

section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem freeQuot_exists_smul_mem (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.SecondBlockLemmaK.goal1 S hx

theorem freeQuot_rank_span (S : Submodule R X) :
    Module.rank R S = Module.rank F (Submodule.span F (S : Set X)) := by
  set T := Submodule.span F (S : Set X)
  have hST : S ≤ T.restrictScalars R := fun x hx => Submodule.subset_span hx
  let S' : Submodule R (T.restrictScalars R) := S.comap (T.restrictScalars R).subtype
  have h0 : Module.rank R ((T.restrictScalars R) ⧸ S') = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S' q
    obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem S (y.2 : (y : X) ∈ T)
    refine ⟨d, hd, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hd'
  have h1 := rank_quotient_add_rank_of_isDomain S'
  rw [h0, zero_add, (Submodule.comapSubtypeEquivOfLe hST).rank_eq] at h1
  rw [h1, IsLocalization.rank_eq (N := T) F (nonZeroDivisors R) le_rfl]
  rfl

end

theorem freeQuot_holds : FreeQuotStatement := by
  intro R F X _ _ _ _ _ _ _ _ _ _ M₁ hM₁ N
  have : Module.Finite R M₁ := Module.Finite.iff_fg.mpr hM₁
  have ne : ∀ r : R, r ≠ 0 → algebraMap R F r ≠ 0 := fun r hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  have htf : Module.IsTorsionFree R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r q hq
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    have hq' : algebraMap R F r • (m : X) ∈ N := by
      rw [algebraMap_smul]
      simpa using hq
    show (m : X) ∈ N
    have h2 := N.smul_mem (algebraMap R F r)⁻¹ hq'
    rwa [smul_smul, inv_mul_cancel₀ (ne r hr), one_smul] at h2
  refine ⟨inferInstance, ?_⟩
  have hspan : Submodule.span F ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) =
      Submodule.span F (M₁ : Set X) ⊓ N := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr ⟨Submodule.subset_span hx1, hx2⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem M₁ hx1
      have hN : d • x ∈ N := by
        rw [← algebraMap_smul F d x]
        exact N.smul_mem _ hx2
      have hmem : d • x ∈ Submodule.span F
          ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) :=
        Submodule.subset_span (Submodule.mem_inf.mpr ⟨hd', hN⟩)
      rw [← algebraMap_smul F d x] at hmem
      have h2 := Submodule.smul_mem _ (algebraMap R F d)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (ne d hd), one_smul] at h2
  have hrn := Submodule.finrank_quotient_add_finrank ((N.restrictScalars R).comap M₁.subtype)
  have hM : finrank R M₁ = finrank F (Submodule.span F (M₁ : Set X)) :=
    congrArg Cardinal.toNat (freeQuot_rank_span M₁)
  have hP : finrank R ((N.restrictScalars R).comap M₁.subtype) =
      finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) := by
    rw [(Submodule.equivMapOfInjective M₁.subtype M₁.injective_subtype
      ((N.restrictScalars R).comap M₁.subtype)).finrank_eq, Submodule.map_comap_subtype, ← hspan]
    exact congrArg Cardinal.toNat (freeQuot_rank_span _)
  rw [← hP, ← hM]
  exact hrn

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
