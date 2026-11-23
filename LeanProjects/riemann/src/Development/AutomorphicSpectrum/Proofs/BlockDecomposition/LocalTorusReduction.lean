import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFTor

open Ad3 Ad3.LFS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem norm_mp_half (x : Fˣ) :
    ‖mp x (1 / 2)‖ = (modulus (x : F) : ℝ) ^ (1 / 2 : ℝ) := by
  have ht : 0 < (modulus (x : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos x.ne_zero
  unfold mp
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
  norm_num

theorem rpow_torus {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a * b) ^ (1 / 2 : ℝ) * (a ^ (1 / 4 : ℝ) * b ^ (-(1 / 2) : ℝ)) = a ^ (3 / 4 : ℝ) := by
  rw [Real.mul_rpow ha.le hb.le, Real.rpow_neg hb.le]
  have hb' : b ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  have : a ^ (3 / 4 : ℝ) = a ^ (1 / 2 : ℝ) * a ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add ha]
    norm_num
  rw [this]
  field_simp

theorem gTor : Ad3.LFS.GTor := by
  intro hT hF hI F _ _ _ _ _ _ ψ ν W' Φ hyp
  obtain ⟨hs, hu, ⟨V', hV, hW⟩, hΦ⟩ := id hyp
  obtain ⟨C₁, R, h1⟩ := hF F ψ hs Φ hΦ
  obtain ⟨C₂, h2⟩ := hI F ψ hs ν hu V' hV W' hW R
  refine ⟨max C₁ 0 * max C₂ 0, fun t₁ t₂ => ?_⟩
  obtain ⟨hint, hle⟩ := h2 t₁ t₂
  have hm1 : 0 < (modulus (t₁ : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos t₁.ne_zero
  have hm2 : 0 < (modulus (t₂ : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos t₂.ne_zero
  have hC₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  set G : GL (Fin 2) F → ℝ := (om R t₂).indicator fun k =>
    ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)
    with hGd
  have hG0 : ∀ k, 0 ≤ G k := fun k =>
    Set.indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) k
  have hpt : ∀ k : GL (Fin 2) F,
      ‖W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
          (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)‖ ≤
        max C₁ 0 * G k := by
    intro k
    by_cases hp : pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) = 0
    · rw [hp, mul_zero, norm_zero]
      exact mul_nonneg hC₁ (hG0 k)
    · obtain ⟨hb, hsup⟩ := h1 (k : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)
      obtain ⟨hk, hξ⟩ := hsup hp
      have hmem : k ∈ om R t₂ := ⟨hk, hξ⟩
      have hGk : G k = ‖W' (dg2 t₁ t₂ * k⁻¹)‖ *
          (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hGd, Set.indicator_of_mem hmem]
      rw [norm_mul, norm_mul, norm_mp_half, ← hGk, mul_comm]
      exact mul_le_mul ((hb).trans (le_max_left _ _)) le_rfl
        (by rw [hGk]; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) hC₁
  have hbound : ‖∫ k, W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
          (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) ∂hG ψ‖ ≤
      max C₁ 0 * (max C₂ 0 * ((modulus (t₁ : F) : ℝ) ^ (1 / 4 : ℝ) *
        (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono := integral_mono_of_nonneg (μ := hG ψ)
      (Filter.Eventually.of_forall fun k => norm_nonneg _)
      (hint.const_mul (max C₁ 0)) (Filter.Eventually.of_forall hpt)
    refine hmono.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    refine hle.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (Real.rpow_nonneg hm1.le _) (Real.rpow_nonneg hm2.le _))
  rw [hT F ψ ν W' Φ hyp t₁ t₂, norm_mul, norm_mp_half, Units.val_mul, GroundTheory.LocalField.modulus_mul,
    NNReal.coe_mul]
  calc _ ≤ ((modulus (t₁ : F) : ℝ) * modulus (t₂ : F)) ^ (1 / 2 : ℝ) *
        (max C₁ 0 * (max C₂ 0 * ((modulus (t₁ : F) : ℝ) ^ (1 / 4 : ℝ) *
          (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = max C₁ 0 * max C₂ 0 * (((modulus (t₁ : F) : ℝ) * modulus (t₂ : F)) ^ (1 / 2 : ℝ) *
          ((modulus (t₁ : F) : ℝ) ^ (1 / 4 : ℝ) * (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ))) := by ring
    _ = _ := by rw [rpow_torus hm1 hm2]

end GlobalTheory.CompanionTheory.LFTor
