import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.TTRANS
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.GL2Classical.GrowthReduction
import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.IwasawaBound

open Matrix GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem exists_adelicNorm_vecMul_le_mul (h : G2) : ∃ C : ℝ, 1 ≤ C ∧ ∀ y : Fin 2 → 𝔸[ℚ],
    HasFiniteContent y → adelicNorm (y ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])) ≤ C * adelicNorm y := by
  have hb1 : ∀ v, v ∉ (finite_mulSupport_locHeight_finAt h).toFinset →
      locHeight (finAt v h) = 1 := fun v hv => by
    by_contra hne
    exact hv ((finite_mulSupport_locHeight_finAt h).mem_toFinset.2 hne)
  refine ⟨max 1 ((∏ w : InfinitePlace ℚ, (√((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * locHeight (infAt w h))) ^ w.mult) *
    ∏ v ∈ (finite_mulSupport_locHeight_finAt h).toFinset, locHeight (finAt v h)),
    le_max_left _ _, fun y hy => ?_⟩
  have hinf : ∀ w, euclidNorm (infComp w (y ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]))) ≤
      √((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * locHeight (infAt w h)) * euclidNorm (infComp w y) := fun w => by
    rw [infComp_vecMul_GL]
    exact euclidNorm_vecMul_le (locHeight_pos _).le (fun i j => norm_apply_le_locHeight _ i j) _
  have hfin : ∀ v, ‖finComp v (y ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]))‖ ≤
      locHeight (finAt v h) * ‖finComp v y‖ := fun v => by
    rw [finComp_vecMul_GL]
    exact norm_vecMul_le_of_norm_le v (locHeight_pos _).le
      (fun i j => norm_apply_le_locHeight _ i j) _
  have key := adelicNorm_le_of_local (hy.vecMul h) hy
    (fun w => √((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) * locHeight (infAt w h)))
    (fun v => locHeight (finAt v h)) (finite_mulSupport_locHeight_finAt h).toFinset hinf hb1 hfin
  exact key.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (adelicNorm_nonneg _))

theorem exists_eq_pt (g : G2) : ∃ (x : 𝔸[ℚ]) (a z : Jd) (κ : KA), g = pt x a z κ.1 := by
  obtain ⟨b, hb, k, hk, rfl⟩ := exists_adelicBorel_mul_maxCompact g
  obtain ⟨α, hα⟩ := isUnit_apply_self_of_mem_adelicBorel hb 0
  obtain ⟨δ, hδ⟩ := isUnit_apply_self_of_mem_adelicBorel hb 1
  have h10 : (b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 0 = 0 := hb (show (0 : Fin 2) < 1 by decide)
  refine ⟨(b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 1 * ((δ⁻¹ : Jd) : 𝔸[ℚ]), α * δ⁻¹, δ, ⟨k, hk⟩, ?_⟩
  have hb' : b = uni2 ((b : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 1 * ((δ⁻¹ : Jd) : 𝔸[ℚ])) *
      dg2 (α * δ⁻¹) 1 * dg2 δ δ := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, hα, hδ, h10]
    · rw [← hδ, mul_assoc, Units.inv_mul, mul_one]
    · rw [← hδ, mul_assoc, Units.inv_mul, mul_one]
  show b * k = uni2 _ * dg2 _ 1 * dg2 _ _ * k
  rw [← hb']

theorem lower_row_pt (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) :
    (Pi.single 1 (1 : 𝔸[ℚ]) : Fin 2 → 𝔸[ℚ]) ᵥ* (pt x a z κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
      ((z : 𝔸[ℚ]) • (Pi.single 1 (1 : 𝔸[ℚ]) : Fin 2 → 𝔸[ℚ])) ᵥ* (κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) := by
  have h : (Pi.single 1 (1 : 𝔸[ℚ]) : Fin 2 → 𝔸[ℚ]) ᵥ*
      ((uni2 x * dg2 a 1 * dg2 z z : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
      (z : 𝔸[ℚ]) • (Pi.single 1 (1 : 𝔸[ℚ]) : Fin 2 → 𝔸[ℚ]) := by
    ext1 j
    fin_cases j <;> simp [uni2, dg2, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← h, vecMul_vecMul, ← Units.val_mul]
  rfl

theorem det_pt (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) :
    GeneralLinearGroup.det (pt x a z κ) = a * z * z * GeneralLinearGroup.det κ := by
  have h1 : GeneralLinearGroup.det (uni2 x) = 1 := by
    apply Units.ext
    simp [uni2, Matrix.det_fin_two]
  have h2 : ∀ c d : Jd, GeneralLinearGroup.det (dg2 c d) = c * d := fun c d => by
    apply Units.ext
    simp [dg2, Matrix.det_fin_two]
  simp only [pt, map_mul, h1, h2, one_mul, mul_one]
  simp only [mul_assoc]

theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md]

theorem real_bound {B t m A : ℝ} (hB : 1 ≤ B) (ht : 0 < t) (hm1 : B⁻¹ ≤ m) (hm2 : m ≤ B)
    (hA : t = A * m ^ 2) :
    (B ^ 2 * max 1 (max t t⁻¹))⁻¹ ≤ A ∧ A ≤ B ^ 2 * max 1 (max t t⁻¹) ∧
      (B ^ 2 * max 1 (max t t⁻¹))⁻¹ ≤ m ∧ m ≤ B ^ 2 * max 1 (max t t⁻¹) ∧
      1 ≤ B ^ 2 * max 1 (max t t⁻¹) := by
  set T := max 1 (max t t⁻¹) with hT
  have hB0 : 0 < B := by linarith
  have hT1 : 1 ≤ T := le_max_left _ _
  have hT0 : 0 < T := by linarith
  have htT : t ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have htT' : t⁻¹ ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hm0 : 0 < m := lt_of_lt_of_le (inv_pos.2 hB0) hm1
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hC : B ≤ B ^ 2 * T := by nlinarith [sq_nonneg B]
  have hC1 : 1 ≤ B ^ 2 * T := hB.trans hC
  have hC0 : 0 < B ^ 2 * T := by linarith
  have hmB : 1 ≤ B * m := by
    have := mul_le_mul_of_nonneg_left hm1 hB0.le
    rwa [mul_inv_cancel₀ hB0.ne'] at this
  have hAe : A = t / m ^ 2 := by
    field_simp
    linarith
  have hinvm : (m ^ 2)⁻¹ ≤ B ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : (1 : ℝ) ≤ (B * m) ^ 2 := one_le_pow₀ hmB
    nlinarith
  have hm2' : m ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hm0.le hm2 2
  refine ⟨?_, ?_, ?_, hm2.trans hC, hC1⟩
  · rw [inv_le_comm₀ hC0 (by rw [hAe]; positivity), hAe, inv_div, div_eq_mul_inv]
    exact mul_le_mul hm2' htT' (inv_pos.2 ht).le (by positivity)
  · rw [hAe, div_eq_mul_inv, mul_comm]
    exact mul_le_mul hinvm htT ht.le (by positivity)
  · calc (B ^ 2 * T)⁻¹ ≤ B⁻¹ := inv_anti₀ hB0 hC
      _ ≤ m := hm1

theorem iwasawa_coordinates_bounded :
    ∀ h : Ad3.R.G2, ∃ C : ℝ, 1 ≤ C ∧ ∀ κ : Ad3.R.KA, ∃ (x : 𝔸[ℚ]) (a z : Ad3.R.Jd) (κ' : Ad3.R.KA),
      κ.1 * h = Ad3.R.pt x a z κ'.1 ∧ C⁻¹ ≤ md a ∧ md a ≤ C ∧
        C⁻¹ ≤ md z ∧ md z ≤ C := by
  intro h
  obtain ⟨C₁, h1, hC₁⟩ := exists_adelicNorm_vecMul_le_mul h
  obtain ⟨C₂, h2, hC₂⟩ := exists_adelicNorm_vecMul_le_mul h⁻¹
  set B := max C₁ C₂ with hBdef
  have hB : 1 ≤ B := h1.trans (le_max_left _ _)
  set t := md (GeneralLinearGroup.det h) with htdef
  have ht : 0 < t := (IdeleGroup.ideleModule ℚ _).2
  refine ⟨B ^ 2 * max 1 (max t t⁻¹), ?_, fun κ => ?_⟩
  · have : (1 : ℝ) ≤ B ^ 2 := one_le_pow₀ hB
    exact one_le_mul_of_one_le_of_one_le this (le_max_left _ _)
  obtain ⟨x, a, z, κ', he⟩ := exists_eq_pt (κ.1 * h)
  have hfc : HasFiniteContent (Pi.single 1 (1 : 𝔸[ℚ]) : Fin 2 → 𝔸[ℚ]) := hasFiniteContent_single_one 1
  set y : Fin 2 → 𝔸[ℚ] := (Pi.single 1 (1 : 𝔸[ℚ]) : Fin 2 → 𝔸[ℚ]) ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) with hy
  have hyfc : HasFiniteContent y := hfc.vecMul κ.1
  have hy1 : adelicNorm y = 1 := by
    rw [hy, adelicNorm_vecMul_maxCompact _ κ.2, adelicNorm_single_one]
  have hyh : y ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
      ((z : 𝔸[ℚ]) • (Pi.single 1 (1 : 𝔸[ℚ]) : Fin 2 → 𝔸[ℚ])) ᵥ* (κ'.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) := by
    rw [← lower_row_pt x a z κ'.1, ← he, hy, vecMul_vecMul, Units.val_mul]
  have hnorm : adelicNorm (y ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])) = md z := by
    rw [hyh, adelicNorm_vecMul_maxCompact _ κ'.2, adelicNorm_smul hfc, adelicNorm_single_one, mul_one]
    rfl
  have hz0 : 0 < md z := (IdeleGroup.ideleModule ℚ _).2
  have hup : md z ≤ B := by
    have := hC₁ y hyfc
    rw [hnorm, hy1, mul_one] at this
    exact this.trans (le_max_left _ _)
  have hlow : B⁻¹ ≤ md z := by
    have := hC₂ _ (hyfc.vecMul h)
    rw [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, hy1, hnorm] at this
    have hB0 : 0 < B := by linarith
    have h3 : 1 ≤ B * md z := this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hz0.le)
    rw [inv_le_iff_one_le_mul₀ hB0]
    linarith
  have hdet : t = md a * md z ^ 2 := by
    have e := congrArg GeneralLinearGroup.det he
    rw [map_mul, det_pt] at e
    have e' := congrArg md e
    have k1 : md (GeneralLinearGroup.det κ.1) = 1 := by
      have := GroundTheory.Automorphic.Adele2.ideleModule_det_of_mem_maxCompact κ.2
      simp [md, this]
    have k2 : md (GeneralLinearGroup.det κ'.1) = 1 := by
      have := GroundTheory.Automorphic.Adele2.ideleModule_det_of_mem_maxCompact κ'.2
      simp [md, this]
    rw [md_mul, md_mul, md_mul, md_mul, k1, k2] at e'
    rw [htdef]
    nlinarith
  obtain ⟨b1, b2, b3, b4, -⟩ := real_bound hB ht hlow hup hdet
  exact ⟨x, a, z, κ', he, b1, b2, b3, b4⟩

end GlobalTheory.CompanionTheory.IwasawaBound
