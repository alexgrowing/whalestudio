import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.BottomRowCoordinates

theorem md_pos (a : Jd) : 0 < md a := (IdeleGroup.ideleModule ℚ a).2

theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem continuous_Dt : Continuous Dt :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det ℚ 2))

theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  simp only [Dt, map_mul, md_mul]

theorem detModulus_rational (γ : GL (Fin 2) ℚ) : Dt (dia2 γ) = 1 := by
  have h : GeneralLinearGroup.det (dia2 γ) = IdeleGroup.diagonal ℚ (GeneralLinearGroup.det γ) := by
    ext
    rw [IdeleGroup.coe_diagonal, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  simp only [Dt, md, h, IdeleGroup.ideleModule_diagonal]
  rfl

theorem detModulus_unipotent (x : 𝔸[ℚ]) : Dt (uni2 x) = 1 := by
  have h : GeneralLinearGroup.det (uni2 x) = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, uni2, Matrix.det_fin_two]
  simp [Dt, md, h]

theorem detModulus_diag (a b : Jd) : Dt (dg2 a b) = md a * md b := by
  have h : GeneralLinearGroup.det (dg2 a b) = a * b := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, dg2, Matrix.det_fin_two]
  simp [Dt, h, md_mul]

theorem Dt_K (κ : KA) : Dt κ.1 = 1 := by
  have h := GroundTheory.Automorphic.Adele2.ideleModule_det_of_mem_maxCompact κ.2
  simp [Dt, md, h]

theorem Dt_pt (x : 𝔸[ℚ]) (a z : Jd) (κ : KA) : Dt (pt x a z κ.1) = md a * md z ^ 2 := by
  simp only [pt, Dt_mul, detModulus_unipotent, detModulus_diag, Dt_K]
  have : md 1 = 1 := by simp [md]
  rw [this]; ring

theorem central_diagonal_commute (z : Jd) (g : G2) : g * dg2 z z = dg2 z z * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem pt_eq (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) :
    pt x a z κ = dg2 z z * (uni2 x * dg2 a 1 * κ) := by
  simp only [pt]
  rw [central_diagonal_commute z (uni2 x * dg2 a 1)]
  group

theorem row_rational_matrix_mul (ξ : Fin 2 → ℚ) (γ : GL (Fin 2) ℚ) (g : G2) :
    Ad3.R.row ξ (dia2 γ * g) = Ad3.R.row (ξ ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ)) g := by
  simp only [Ad3.R.row, Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, AdelicGLn.diagonal_apply]

def rowEquiv (γ : GL (Fin 2) ℚ) : NZ ≃ NZ where
  toFun ξ := ⟨ξ.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ), fun h => ξ.2 (by
    have := congrArg (· ᵥ* ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using this)⟩
  invFun ξ := ⟨ξ.1 ᵥ* ((γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ), fun h => ξ.2 (by
    have := congrArg (· ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℚ)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using this)⟩
  left_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul, ← Units.val_mul])
  right_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul, ← Units.val_mul])

theorem th_linv (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) : LInv (th Φ) := by
  intro γ g
  simp only [th, row_rational_matrix_mul]
  exact (rowEquiv γ).tsum_eq (fun ξ : NZ => Φ (Ad3.R.row ξ.1 g))

theorem continuous_row (ξ : Fin 2 → ℚ) : Continuous (Ad3.R.row ξ) :=
  Continuous.matrix_vecMul continuous_const Units.continuous_val

theorem measurable_th {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (hΦ : Continuous Φ) : Measurable (th Φ) :=
  Measurable.tsum fun ξ : NZ => (hΦ.comp (continuous_row ξ.1)).measurable

theorem real_id {u w σ : ℝ} (hu : 0 < u) (hw : 0 < w) :
    (u * w ^ 2) ^ σ * u⁻¹ = u ^ (σ - 1) * w ^ (2 * σ) := by
  rw [Real.mul_rpow hu.le (by positivity), Real.rpow_sub_one hu.ne', div_eq_mul_inv]
  have : (w ^ 2) ^ σ = w ^ (2 * σ) := by
    rw [← Real.rpow_natCast w 2, ← Real.rpow_mul hw.le]; norm_num
  rw [this]; ring

theorem point_bound {H : G2 → ℂ} (hH : Aut H) {M : ℕ} {Cd : ℝ}
    (hCd : ∀ x (a : Jd) (κ : KA), ‖H (uni2 x * dg2 a 1 * κ.1)‖ ≤ Cd * min 1 (md a)⁻¹ ^ M)
    (σ : ℝ) (x : 𝔸[ℚ]) (a z : Jd) (κ : KA) (P : ℝ≥0∞) :
    (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * P * ENNReal.ofReal (md a)⁻¹ ≤
      (ENNReal.ofReal Cd * ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ (σ - 1))) *
        (P * ENNReal.ofReal (md z ^ (2 * σ))) := by
  have hu := md_pos a
  have hw := md_pos z
  have hm : 0 ≤ min 1 (md a)⁻¹ ^ M := by positivity
  have hE : ‖H (pt x a z κ.1)‖ₑ ≤ ENNReal.ofReal Cd * ENNReal.ofReal (min 1 (md a)⁻¹ ^ M) := by
    rw [pt_eq, hH.cen, ← ENNReal.ofReal_mul' hm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hCd x a κ)
  have e1 : ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ) * ENNReal.ofReal (md a)⁻¹ =
      ENNReal.ofReal (md a ^ (σ - 1)) * ENNReal.ofReal (md z ^ (2 * σ)) := by
    rw [Dt_pt, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), real_id hu hw]
  have e2 : ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ (σ - 1)) =
      ENNReal.ofReal (min 1 (md a)⁻¹ ^ M) * ENNReal.ofReal (md a ^ (σ - 1)) :=
    ENNReal.ofReal_mul hm
  calc (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * P * ENNReal.ofReal (md a)⁻¹
      = ‖H (pt x a z κ.1)‖ₑ * (ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ) * ENNReal.ofReal (md a)⁻¹) * P := by ring
    _ ≤ (ENNReal.ofReal Cd * ENNReal.ofReal (min 1 (md a)⁻¹ ^ M)) *
          (ENNReal.ofReal (md a ^ (σ - 1)) * ENNReal.ofReal (md z ^ (2 * σ))) * P := by
        rw [e1]; gcongr
    _ = _ := by rw [e2]; ring

theorem g3 : Ad3.R.G2a → Ad3.R.G2b → Ad3.R.G3a → Ad3.R.G3 := by
  intro h2a h2b h3a μ 𝓕 mK 𝓓 hS H hH Φ hΦ σ hσ
  obtain ⟨C, hC⟩ := h2a μ 𝓕 mK 𝓓 hS
  obtain ⟨hΦc, hΦb⟩ := h3a Φ hΦ
  refine ⟨measurable_th hΦc, th_linv Φ, ?_⟩
  haveI := hS.probK
  have hHm : Measurable fun g => ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ) :=
    hH.cont.enorm.measurable.mul ((continuous_Dt.measurable.pow_const σ).ennreal_ofReal)
  have hHl : LInv fun g => ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ) := by
    intro γ g
    simp only [hH.left γ g, Dt_mul, detModulus_rational, one_mul]
  rw [h2b μ 𝓕 mK 𝓓 C hS hC (fun g => ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)) (fun r => ‖Φ r‖ₑ)
    hHm hHl hΦc.enorm.measurable]
  obtain ⟨Cd, hCd⟩ := hH.dec ⌈σ⌉₊
  obtain ⟨CB, hCB, hB⟩ := hΦb (2 * σ) (by linarith)
  have hMσ : σ - 1 < (⌈σ⌉₊ : ℝ) := by linarith [Nat.le_ceil σ]
  set A : Jd → ℝ≥0∞ := fun a =>
    ENNReal.ofReal Cd * ENNReal.ofReal (min 1 (md a)⁻¹ ^ ⌈σ⌉₊ * md a ^ (σ - 1)) with hA
  set B : Jd → KA → ℝ≥0∞ := fun z κ => ‖Φ (lrow z κ.1)‖ₑ * ENNReal.ofReal (md z ^ (2 * σ)) with hBdef
  have hIA : ∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ < ∞ := by
    simp only [hA]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hS.finD (σ - 1) ⌈σ⌉₊ (by linarith) hMσ)
  have hBne : ∀ z κ, B z κ ≠ ∞ := fun z κ =>
    ENNReal.mul_ne_top enorm_ne_top ENNReal.ofReal_ne_top
  have hx : ∀ (κ : KA) (z a : Jd), ∫⁻ x in fundamentalSet ℚ,
      (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * ‖Φ (lrow z κ.1)‖ₑ *
        ENNReal.ofReal (md a)⁻¹ ∂adeleMeasure ℚ ≤ A a * B z κ := by
    intro κ z a
    calc _ ≤ ∫⁻ _ in fundamentalSet ℚ, A a * B z κ ∂adeleMeasure ℚ :=
          lintegral_mono fun x => point_bound hH hCd σ x a z κ _
      _ = A a * B z κ := by
          rw [setLIntegral_const, adeleMeasure_fundamentalSet, mul_one]
  have ha : ∀ (κ : KA) (z : Jd), ∫⁻ a in 𝓓, ∫⁻ x in fundamentalSet ℚ,
      (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * ‖Φ (lrow z κ.1)‖ₑ *
        ENNReal.ofReal (md a)⁻¹ ∂adeleMeasure ℚ ∂ideleMeasure ℚ ≤
        (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * B z κ := by
    intro κ z
    calc _ ≤ ∫⁻ a in 𝓓, A a * B z κ ∂ideleMeasure ℚ := lintegral_mono fun a => hx κ z a
      _ = _ := lintegral_mul_const' _ _ (hBne z κ)
  have hz : ∀ κ : KA, ∫⁻ z, ∫⁻ a in 𝓓, ∫⁻ x in fundamentalSet ℚ,
      (‖H (pt x a z κ.1)‖ₑ * ENNReal.ofReal (Dt (pt x a z κ.1) ^ σ)) * ‖Φ (lrow z κ.1)‖ₑ *
        ENNReal.ofReal (md a)⁻¹ ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ ≤
        (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * CB := by
    intro κ
    calc _ ≤ ∫⁻ z, (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * B z κ ∂ideleMeasure ℚ :=
          lintegral_mono fun z => ha κ z
      _ = (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * ∫⁻ z, B z κ ∂ideleMeasure ℚ :=
          lintegral_const_mul' _ _ hIA.ne
      _ ≤ _ := by gcongr; exact hB κ
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  calc _ ≤ ∫⁻ _ : KA, (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * CB ∂mK := lintegral_mono hz
    _ = (∫⁻ a in 𝓓, A a ∂ideleMeasure ℚ) * CB := by simp
    _ < ∞ := ENNReal.mul_lt_top hIA hCB

end GlobalTheory.CompanionTheory.BottomRowCoordinates

end
