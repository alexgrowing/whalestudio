import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.Reduction
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GlobalTheory.HCF

theorem exists_siegel_band : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ), ∃ Ω : Set (GA E a), IsCompact Ω ∧ Ω ⊆ ((adelicBorel : Subgroup (GA E a)) : Set (GA E a)) ∧ ∃ t c₁ c₂ : ℝ, 0 < t ∧ 0 < c₁ ∧ ∀ g ∈ band E a, ∃ γ : GL (Fin a) E, ∃ b ∈ Ω, ∃ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧ c₁ ≤ ∏ i, r i ∧ ∏ i, r i ≤ c₂ ∧ ∃ k ∈ (maxCompact : Subgroup (GA E a)), ratGL E a γ * g = b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k := by
  intro E _ _ a
  obtain ⟨W0, hW, hWB, t, ht, h⟩ := exists_siegelSet (K := E) a
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := exists_pos_bounds hW
    (f := fun b => (ideleModule E (AdelicGLn.det E a b) : ℝ))
    (continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E a)))
    (fun b _ => (ideleModule E (AdelicGLn.det E a b)).2)
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  set X₁ : ℝ := min 1 B₂⁻¹ with hX₁def
  set X₂ : ℝ := max 1 (2 / B₁) with hX₂def
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  refine ⟨W0, hW, hWB, t, X₁, X₂, ht, hX₁, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := h g
  obtain ⟨b, hbW, _, ⟨r, hr, hrat, rfl⟩, k, hk, hgeq⟩ := hγ
  have hgmod : (ideleModule E (AdelicGLn.det E a g) : ℝ) = absDetA g := (adeleAbs_units _).symm
  have hmod := congrArg (fun x => (ideleModule E (AdelicGLn.det E a x) : ℝ)) hgeq
  rw [det_mul_mul, ideleModule_det_diagUnits_posIdele r hr,
    mem_normOneGL.1 (maxCompact_le_normOneGL hk), mul_one, map_mul, map_mul, Positive.val_mul,
    mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩), one_mul, hgmod] at hmod
  set X : ℝ := ∏ i, r i with hX
  have hXpos : 0 < X := Finset.prod_pos fun i _ => hr i
  have hb := hB b hbW
  obtain ⟨h1, h2⟩ := hg
  have hXd1 : X ^ d ≤ 2 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc X ^ d * B₁ ≤ X ^ d * (ideleModule E (AdelicGLn.det E a b) : ℝ) :=
          mul_le_mul_of_nonneg_left hb.1 (pow_nonneg hXpos.le _)
      _ = absDetA g := by rw [mul_comm, hmod]
      _ ≤ 2 := h2
  have hXd2 : B₂⁻¹ ≤ X ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ = (ideleModule E (AdelicGLn.det E a b) : ℝ) * X ^ d := hmod
      _ ≤ B₂ * X ^ d := mul_le_mul_of_nonneg_right hb.2 (pow_nonneg hXpos.le _)
  have hratGL : ratGL E a γ = AdelicGLn.diagonal E a γ := rfl
  refine ⟨γ, b, hbW, r, hr, hrat, ?_, ?_, k, hk, by rw [hratGL]; exact hgeq⟩
  · rcases le_or_gt 1 X with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hXd2.trans (pow_le_of_le_one hXpos.le h.le hd0.ne'))
  · rcases le_or_gt X 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hXd1.trans (le_max_right _ _))
end GlobalTheory.HCF
