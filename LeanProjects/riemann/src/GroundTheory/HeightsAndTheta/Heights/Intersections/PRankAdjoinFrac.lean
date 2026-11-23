import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRankAdjoinFrac
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Module IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace RankAdjoinFrac

theorem finrank_algebraAdjoin_eq_finrank_adjoin {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (T : Set Ω) :
    finrank K (Algebra.adjoin K T) = finrank K (IntermediateField.adjoin K T) := by
  by_cases hT : ∀ x ∈ T, IsAlgebraic K x
  · rw [← IntermediateField.finrank_eq_finrank_subalgebra, adjoin_toSubalgebra_of_isAlgebraic hT]
  · push Not at hT
    obtain ⟨x, hx, hnx⟩ := hT
    have h1 : finrank K (Algebra.adjoin K T) = 0 := by
      by_contra h0
      have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h0)
      exact hnx ((Algebra.IsAlgebraic.isAlgebraic
        (⟨x, Algebra.subset_adjoin hx⟩ : Algebra.adjoin K T)).algHom (Algebra.adjoin K T).val)
    have h2 : finrank K (IntermediateField.adjoin K T) = 0 := by
      by_contra h0
      have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h0)
      exact hnx ((Algebra.IsAlgebraic.isAlgebraic
        (⟨x, subset_adjoin K T hx⟩ : IntermediateField.adjoin K T)).algHom (IntermediateField.adjoin K T).val)
    rw [h1, h2]

theorem exists_mul_mem_of_mem {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) {y : Ω}
    (hy : y ∈ Algebra.adjoin (IntermediateField.adjoin F S) T) :
    ∃ a ∈ Algebra.adjoin F S, a ≠ 0 ∧ a * y ∈ Algebra.adjoin F T := by
  have hST := Algebra.adjoin_mono (R := F) h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_mem _, one_ne_zero, by rw [one_mul]; exact Algebra.subset_adjoin hx⟩
  | algebraMap k =>
    obtain ⟨r, hr, s, hs, hk⟩ := mem_adjoin_iff_div.mp k.2
    by_cases hs0 : s = 0
    · refine ⟨1, one_mem _, one_ne_zero, ?_⟩
      have : (algebraMap (IntermediateField.adjoin F S) Ω k) = 0 := by
        change (k : Ω) = 0
        rw [hk, hs0, div_zero]
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨s, hs, hs0, ?_⟩
      change s * (k : Ω) ∈ _
      rw [hk, mul_div_cancel₀ _ hs0]
      exact hST hr
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x + y) = b * (a * x) + a * (b * y) := by ring
    rw [this]
    exact add_mem (mul_mem (hST hb) hax) (mul_mem (hST ha) hby)
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x * y) = (a * x) * (b * y) := by ring
    rw [this]
    exact mul_mem hax hby

theorem finrank_eq_finrank_algebraAdjoin {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω}
    (h : S ⊆ T) :
    letI := adjoinInclAlgebra F h
    finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
  let _ := adjoinInclAlgebra F h
  let _ : Algebra (Algebra.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    ((algebraMap (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T)).comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S)
      (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hle : Algebra.adjoin F T ≤ (Algebra.adjoin (IntermediateField.adjoin F S) T).restrictScalars F :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := IntermediateField.adjoin F S))
  let f : Algebra.adjoin F T →ₗ[Algebra.adjoin F S] Algebra.adjoin (IntermediateField.adjoin F S) T :=
    { toFun := fun m => ⟨m.1, hle m.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        apply Subtype.ext
        simp only [Algebra.smul_def, RingHom.id_apply, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_inclusion] }
  have : IsLocalizedModule (nonZeroDivisors (Algebra.adjoin F S)) f := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
    · rw [Module.End.isUnit_iff]
      have hx0 : algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (Algebra.adjoin F S) (IntermediateField.adjoin F S))).mpr
          (nonZeroDivisors.coe_ne_zero x)
      refine ⟨fun u v huv => ?_, fun v => ?_⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) u,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) v] at huv
        calc u = (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ •
              (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x • u) := by
                rw [smul_smul, inv_mul_cancel₀ hx0, one_smul]
          _ = v := by rw [huv, smul_smul, inv_mul_cancel₀ hx0, one_smul]
      · refine ⟨(algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ • v, ?_⟩
        rw [Module.algebraMap_end_apply, ← algebraMap_smul (IntermediateField.adjoin F S), smul_smul,
          mul_inv_cancel₀ hx0, one_smul]
    · obtain ⟨a, ha, ha0, hay⟩ := exists_mul_mem_of_mem h y.2
      refine ⟨(⟨a * y, hay⟩, ⟨⟨a, ha⟩, mem_nonZeroDivisors_of_ne_zero ?_⟩), ?_⟩
      · exact fun h0 => ha0 (congrArg Subtype.val h0)
      · apply Subtype.ext
        simp only [Submonoid.smul_def, Algebra.smul_def, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply]
        rfl
    · refine ⟨1, ?_⟩
      rw [one_smul, one_smul]
      exact Subtype.ext (congrArg (fun z : Algebra.adjoin (IntermediateField.adjoin F S) T => (z : Ω)) hx)
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (Algebra.adjoin F S)) f le_rfl,
    IsLocalization.finrank_eq (IntermediateField.adjoin F S) (nonZeroDivisors (Algebra.adjoin F S)) le_rfl]

theorem proof : RankAdjoinFrac.Statement := by
  intro F Ω _ _ _ S T h
  have hKL : IntermediateField.adjoin F S ≤ IntermediateField.adjoin F T := adjoin.mono F S T h
  have hE : extendScalars hKL = IntermediateField.adjoin (IntermediateField.adjoin F S) T :=
    restrictScalars_injective F (by
      rw [extendScalars_restrictScalars, adjoin_adjoin_left, Set.union_eq_self_of_subset_left h])
  have key : IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
    rw [relfinrank_eq_finrank_of_le hKL, hE, finrank_algebraAdjoin_eq_finrank_adjoin]
  exact (finrank_eq_finrank_algebraAdjoin h).trans key.symm

end RankAdjoinFrac

end GroundTheory.Heights₂.Heights.Inter
