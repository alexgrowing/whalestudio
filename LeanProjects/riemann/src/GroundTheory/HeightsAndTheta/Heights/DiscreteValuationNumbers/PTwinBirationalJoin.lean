import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord fnField)

section Proof

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type}

omit [Fintype K] in

theorem BirationalJoin.segre_ratio_mem_fnField (y : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (c₁ c₂ : ∀ k, ι₂ k) : segreVec w c₁ / segreVec w c₂ ∈ fnField O (joinCoord y w) := by
  unfold segreVec
  rw [← Finset.prod_div_distrib]
  refine Subfield.prod_mem _ fun k _ => ?_
  apply Subfield.subset_closure
  refine Or.inr ⟨⟨Sum.inr k, c₁ k, c₂ k⟩, rfl⟩

theorem BirationalJoin.segreVec_update [DecidableEq K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K)
    (i : ι k) :
    segreVec y (Function.update c k i) = y ⟨k, i⟩ * ∏ l ∈ Finset.univ \ {k}, y ⟨l, c l⟩ := by
  unfold segreVec
  have hf : (fun l => y ⟨l, Function.update c k i l⟩) =
      Function.update (fun l => y ⟨l, c l⟩) k (y ⟨k, i⟩) := by
    funext l
    by_cases hl : l = k
    · subst hl
      simp
    · simp [Function.update_of_ne hl]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ k)]

theorem BirationalJoin.fnField_le_closure_chartRing (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) :
    fnField O y ≤ Subfield.closure (chartRing O (segreVec y) c : Set Ω) := by
  classical
  refine Subfield.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
  · have hk : y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
    set P := ∏ l ∈ Finset.univ \ {k}, y ⟨l, c l⟩ with hP
    have hcP : segreVec y c = y ⟨k, c k⟩ * P := by
      have h := BirationalJoin.segreVec_update y c k (c k)
      rwa [Function.update_eq_self] at h
    have hP0 : P ≠ 0 := by
      intro h0
      apply hc
      rw [hcP, h0, mul_zero]
    have hmem : ∀ m : ι k, segreVec y (Function.update c k m) / segreVec y c ∈
        Subfield.closure (chartRing O (segreVec y) c : Set Ω) := fun m =>
      Subfield.subset_closure (Algebra.subset_adjoin ⟨Function.update c k m, rfl⟩)
    have key : y ⟨k, i⟩ / y ⟨k, j⟩ = (segreVec y (Function.update c k i) / segreVec y c) /
        (segreVec y (Function.update c k j) / segreVec y c) := by
      rw [div_div_div_cancel_right₀ hc, BirationalJoin.segreVec_update,
        BirationalJoin.segreVec_update, mul_div_mul_right _ _ hP0]
    show y ⟨k, i⟩ / y ⟨k, j⟩ ∈ _
    rw [key]
    exact Subfield.div_mem _ (hmem i) (hmem j)

theorem BirationalJoin.exists_div_of_mem_closure (S : Subalgebra O Ω) {x : Ω}
    (hx : x ∈ Subfield.closure (S : Set Ω)) : ∃ a ∈ S, ∃ b ∈ S, x = a / b := by
  have hS : Subring.closure (S : Set Ω) = S.toSubring := by
    rw [← Subalgebra.coe_toSubring]
    exact Subring.closure_eq _
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [hS] at ha hb
  exact ⟨a, ha, b, hb, rfl⟩

end Proof

theorem BirationalJoin.proof : BirationalJoin.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ y K₂ _ ι₂ _ w h c hc c₁ c₂ hc₂
  have hr : segreVec w c₁ / segreVec w c₂ ∈ fnField O y :=
    h ▸ BirationalJoin.segre_ratio_mem_fnField y w c₁ c₂
  obtain ⟨a, ha, b, hb, hab⟩ := BirationalJoin.exists_div_of_mem_closure _
    (BirationalJoin.fnField_le_closure_chartRing y c hc hr)
  by_cases hb0 : b = 0
  · have hw : segreVec w c₁ = 0 := by
      rw [hb0, div_zero, div_eq_zero_iff] at hab
      exact hab.resolve_right hc₂
    exact ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, by rw [hw, zero_mul, zero_mul]⟩
  · exact ⟨a, ha, b, hb, hb0, (div_eq_div_iff hc₂ hb0).mp hab⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
