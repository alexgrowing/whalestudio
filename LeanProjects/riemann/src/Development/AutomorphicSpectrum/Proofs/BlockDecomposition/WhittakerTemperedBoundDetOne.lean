import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Row1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformTorusVanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GJTwo.WhB

section L

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem modulus_det_integral {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    modulus ((k.val).det) = 1 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have key : ∀ g : GL (Fin 2) F, (∀ i j, g i j ∈ 𝒪[F]) → modulus ((g.val).det) ≤ 1 := by
    intro g hg
    rw [modulus_le_one_iff, Matrix.det_fin_two]
    exact sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0))
  have a' := key k h1
  have b' := key k⁻¹ h2
  have hne : (k.val).det ≠ 0 := (Matrix.GeneralLinearGroup.det k).ne_zero
  have hinv : ((k⁻¹ : GL (Fin 2) F).val).det = ((k.val).det)⁻¹ := by
    have := congrArg (fun m : GL (Fin 2) F => (m.val).det) (mul_inv_cancel k)
    simp only [Units.val_mul, Matrix.det_mul, Units.val_one, Matrix.det_one] at this
    exact eq_inv_of_mul_eq_one_right this
  rw [hinv, modulus_inv] at b'
  exact le_antisymm a' ((inv_le_one₀ (modulus_pos hne)).1 b')

theorem one_le_modulus_of_comb {c d e f : F} (hc : c ≠ 0) (he : e ∈ 𝒪[F]) (hf : f ∈ 𝒪[F])
    (hdc : modulus d ≤ modulus c) (h : c * e + d * f = 1) : 1 ≤ modulus c := by
  have hpos := modulus_pos hc
  have hq : d / c ∈ 𝒪[F] := by
    rw [← modulus_le_one_iff, div_eq_mul_inv, modulus_mul, modulus_inv]
    exact mul_inv_le_one_of_le₀ hdc (le_of_lt hpos)
  have hi : c⁻¹ = e + d / c * f := by
    field_simp
    linear_combination -h
  have hi' : c⁻¹ ∈ 𝒪[F] := by
    rw [hi]
    exact add_mem he (mul_mem hq hf)
  have := (modulus_le_one_iff).2 hi'
  rw [modulus_inv] at this
  exact (inv_le_one₀ hpos).1 this

theorem mx_bottom_integral {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    mx (fun j => k.val 1 j) = 1 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have hle : ∀ j, (modulus (k.val 1 j) : ℝ) ≤ 1 := fun j => by
    have : modulus (k.val 1 j) ≤ 1 := (modulus_le_one_iff).2 (h1 1 j)
    exact_mod_cast this
  have heq : k.val 1 0 * (k⁻¹ : GL (Fin 2) F).val 0 1 + k.val 1 1 * (k⁻¹ : GL (Fin 2) F).val 1 1 = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) (Units.mul_inv k)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
    exact h
  have hlow : (1 : ℝ) ≤ mx (fun j => k.val 1 j) := by
    unfold mx
    rcases le_total (modulus (k.val 1 0)) (modulus (k.val 1 1)) with hd | hd
    · have hne : k.val 1 1 ≠ 0 := by
        intro h0
        have h00 : k.val 1 0 = 0 := by
          by_contra hx
          have := modulus_pos hx
          rw [h0, modulus_zero] at hd
          exact absurd hd (not_le.2 this)
        rw [h0, h00] at heq
        simp at heq
      have := one_le_modulus_of_comb hne (h2 1 1) (h2 0 1) hd (by linear_combination heq)
      exact le_max_of_le_right (by exact_mod_cast this)
    · have hne : k.val 1 0 ≠ 0 := by
        intro h0
        have h00 : k.val 1 1 = 0 := by
          by_contra hx
          have := modulus_pos hx
          rw [h0, modulus_zero] at hd
          exact absurd hd (not_le.2 this)
        rw [h0, h00] at heq
        simp at heq
      have := one_le_modulus_of_comb hne (h2 0 1) (h2 1 1) hd heq
      exact le_max_of_le_left (by exact_mod_cast this)
  exact le_antisymm (max_le (hle 0) (hle 1)) hlow

theorem mx_iwasawa (x : F) (a b : Fˣ) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    mx (fun j => (uni2 x * dg2 a b * k).val 1 j) = (modulus (b : F) : ℝ) := by
  have hrow : ∀ j, (uni2 x * dg2 a b * k).val 1 j = (b : F) * k.val 1 j := by
    intro j
    simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have h := mx_bottom_integral hk
  unfold mx at h ⊢
  simp only [hrow, modulus_mul, NNReal.coe_mul]
  rw [← mul_max_of_nonneg _ _ (NNReal.coe_nonneg _), h, mul_one]

theorem modulus_mul_of_det_one (x : F) (a b : Fˣ) {k : GL (Fin 2) F}
    (hk : k ∈ GLnLocal.integralGL F 2) (hd : ((uni2 x * dg2 a b * k).val).det = 1) :
    (modulus (a : F) : ℝ) * (modulus (b : F) : ℝ) = 1 := by
  have hdet : ((uni2 x * dg2 a b * k).val).det = (a : F) * b * (k.val).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    simp [uni2, dg2, Matrix.det_fin_two]
  rw [hdet] at hd
  have := congrArg modulus hd
  rw [modulus_mul, modulus_mul, modulus_det_integral hk, mul_one, modulus_one] at this
  exact_mod_cast this

theorem torus_iwasawa (y a b : Fˣ) (x : F) (k : GL (Fin 2) F) :
    dg2 y 1 * (uni2 x * dg2 a b * k) =
      uni2 ((y : F) * x) * (dg2 b b * (dg2 (y * (a * b⁻¹)) 1 * k)) := by
  have e0 : dg2 y 1 * (uni2 x * dg2 a b) =
      uni2 ((y : F) * x) * (dg2 b b * dg2 (y * (a * b⁻¹)) 1) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]
    field_simp
  rw [← mul_assoc (dg2 y 1), e0]
  simp only [mul_assoc]

end L

theorem whittaker_bound_det_one : (ForT fun F _ _ _ _ _ _ ψ ω G V' => ∀ W ∈ V', ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, 0 ≤ C ∧
  ∀ (y : Fˣ) (g : GL (Fin 2) F), (g.val).det = 1 →
    ‖W (dg2 y 1 * g)‖ ≤ C * ((modulus (y : F) : ℝ) / GlobalTheory.CompanionTheory.GJTwo.mx (fun j => g.val 1 j) ^ 2) ^ (1 / 2 - ε) ∧
    (W (dg2 y 1 * g) ≠ 0 → (modulus (y : F) : ℝ) / GlobalTheory.CompanionTheory.GJTwo.mx (fun j => g.val 1 j) ^ 2 ≤ B)) := by
  intro F _ _ _ _ _ _ ψ hψ ω G V' hω H W hW ε hε
  obtain ⟨C, B, hCB⟩ := H.bound W hW ε hε
  refine ⟨max C 0, B, le_max_right _ _, fun y g hg => ?_⟩
  obtain ⟨x, a, b, k, hk, rfl⟩ := GlobalTheory.CompanionTheory.RankinTorusVanishing.exists_iwasawa2 g
  have hab := modulus_mul_of_det_one x a b hk hg
  have hb0 : (0 : ℝ) < modulus (b : F) := by exact_mod_cast modulus_pos b.ne_zero
  set u : Fˣ := y * (a * b⁻¹) with hu
  have hmod : (modulus (y : F) : ℝ) / mx (fun j => (uni2 x * dg2 a b * k).val 1 j) ^ 2 =
      (modulus (u : F) : ℝ) := by
    rw [mx_iwasawa x a b hk, hu]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, modulus_mul, modulus_inv, NNReal.coe_mul,
      NNReal.coe_inv]
    rw [eq_inv_of_mul_eq_one_left hab]
    field_simp
  have hWeq : W (dg2 y 1 * (uni2 x * dg2 a b * k)) =
      (ψ⁻¹ ((y : F) * x) : ℂ) * (((ω b : ℂˣ) : ℂ) * W (dg2 u 1 * k)) := by
    rw [torus_iwasawa, H.psi W hW, H.cen W hW]
  have hnorm : ‖W (dg2 y 1 * (uni2 x * dg2 a b * k))‖ = ‖W (dg2 u 1 * k)‖ := by
    rw [hWeq, norm_mul, norm_mul, Circle.norm_coe, hω.2, one_mul, one_mul]
  rw [hmod]
  obtain ⟨h1, h2⟩ := hCB u k hk
  refine ⟨?_, fun hne => h2 ?_⟩
  · rw [hnorm]
    refine h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
  · intro h0
    apply hne
    rw [hWeq, h0, mul_zero, mul_zero]

end GlobalTheory.CompanionTheory.GJTwo.WhB
