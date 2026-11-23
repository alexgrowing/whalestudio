import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitRepresentationHypothesis
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitPi

open GlobalTheory.CompanionTheory.SplitRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem integral_scale_fst (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ u, G (s * u.1, u.2) ∂muS χ = (((modulus s : ℝ)⁻¹ : ℝ) : ℂ) * ∫ u, G u ∂muS χ := by
  have he1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  have hid : MeasurableEmbedding (id : F → F) := MeasurableEmbedding.id
  have he := he1.prodMap hid
  have hmap : Measure.map (Prod.map (fun x : F => s * x) (id : F → F)) (muS χ) =
      (modulus s)⁻¹ • muS χ := by
    rw [← Measure.map_prod_map _ _ he1.measurable measurable_id,
      map_mul_left_eq_smul _ hs, Measure.map_id, Measure.prod_smul_left]
  have h := he.integral_map (μ := muS χ) G
  rw [hmap, integral_smul_nnreal_measure] at h
  simp only [Prod.map, id] at h
  rw [← h, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring_nf

omit [MeasurableSpace F] [BorelSpace F] in
theorem cjA_det {m : Matrix (Fin 2) (Fin 2) F} (hm : m.det = 1) {A : F} (hA : A ≠ 0) :
    (cjA A m).det = 1 := by
  rw [Matrix.det_fin_two] at hm ⊢
  simp only [cjA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← hm]
  field_simp

theorem dil (χ : AddChar F Circle) {m : Matrix (Fin 2) (Fin 2) F} (hm : m.det = 1) {A : F} (hA : A ≠ 0)
    (Ψ : F × F → ℂ) (y : F × F) :
    rWS χ m Ψ (y * (A, 1)) = rWS χ (cjA A m) (fun v => Ψ (v * (A, 1))) y := by
  have hd := cjA_det hm hA
  have e00 : cjA A m 0 0 = m 0 0 := by simp [cjA]
  have e01 : cjA A m 0 1 = A * m 0 1 := by simp [cjA]
  have e10 : cjA A m 1 0 = m 1 0 / A := by simp [cjA]
  have e11 : cjA A m 1 1 = m 1 1 := by simp [cjA]
  obtain ⟨y1, y2⟩ := y
  by_cases hc : m 1 0 = 0
  · rw [rWS_zero χ hm hc, rWS_zero χ hd (by rw [e10, hc, zero_div]), e00, e01]
    simp only [Prod.mk_mul_mk, mul_one]
    have a1 : m 0 0 * m 0 1 * (y1 * A * y2) = m 0 0 * (A * m 0 1) * (y1 * y2) := by ring
    have a2 : m 0 0 * (y1 * A) = m 0 0 * y1 * A := by ring
    rw [a1, a2]
  · have hcA : cjA A m 1 0 ≠ 0 := by rw [e10]; exact div_ne_zero hc hA
    rw [rWS_ne χ hc, rWS_ne χ hcA, e00, e10, e11]
    simp only [Prod.mk_mul_mk, mul_one]
    set G : F × F → ℂ := fun u =>
      (χ ((m 0 0 * (y1 * A * y2) + m 1 1 * (u.1 * u.2) - (u.1 * y2 + u.2 * (y1 * A))) / m 1 0) : ℂ) * Ψ u
      with hG
    have e1 : ∫ u, (χ ((m 0 0 * (y1 * y2) + m 1 1 * (u.1 * u.2) - (u.1 * y2 + u.2 * y1)) / (m 1 0 / A)) : ℂ) *
        Ψ (u * (A, 1)) ∂muS χ = ∫ u, G (A * u.1, u.2) ∂muS χ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have a : (m 0 0 * (y1 * y2) + m 1 1 * (u.1 * u.2) - (u.1 * y2 + u.2 * y1)) / (m 1 0 / A) =
          (m 0 0 * (y1 * A * y2) + m 1 1 * (A * u.1 * u.2) - (A * u.1 * y2 + u.2 * (y1 * A))) / m 1 0 := by
        field_simp
      have hu : u * ((A, 1) : F × F) = (A * u.1, u.2) := by ext <;> simp [mul_comm]
      simp only [hG, a, hu]
    rw [e1, integral_scale_fst χ hA G]
    have hM : ((modulus A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hA
    rw [div_eq_mul_inv, modulus_mul, modulus_inv]
    push_cast
    field_simp

theorem rWS_const (χ : AddChar F Circle) (m : Matrix (Fin 2) (Fin 2) F) (C : ℂ) (Ψ : F × F → ℂ) :
    rWS χ m (fun z => C * Ψ z) = fun x => C * rWS χ m Ψ x := by
  funext z
  simp only [rWm, rW]
  split_ifs with h
  · ring
  · have e : ∀ u : F × F, ∀ w : ℂ, w * (C * Ψ u) = C * (w * Ψ u) := fun u w => by ring
    simp only [e, integral_const_mul]
    ring

def one1 (h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![h.val 0 0 / (h.val).det, h.val 0 1; h.val 1 0 / (h.val).det, h.val 1 1]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem det_ne (h : GL (Fin 2) F) : (h.val).det ≠ 0 := by
  have := h.isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem det_normalized_determinant_one (h : GL (Fin 2) F) : (one1 h).det = 1 := by
  have hd := det_ne h
  have e := Matrix.det_fin_two h.val
  rw [Matrix.det_fin_two]
  simp only [one1, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  rw [e]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem det_mul' (g h : GL (Fin 2) F) : ((g * h).val).det = (g.val).det * (h.val).det := by
  rw [Units.val_mul, Matrix.det_mul]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem normalized_determinant_cocycle (g h : GL (Fin 2) F) : one1 (g * h) = one1 g * cjA (g.val).det (one1 h) := by
  have hA := det_ne g
  have hB := det_ne h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [one1, cjA, Matrix.mul_apply, Fin.sum_univ_two, det_mul', -Matrix.GeneralLinearGroup.val_det_apply] <;>
    field_simp

def cst (c₁ : Fˣ →* ℂˣ) (h : GL (Fin 2) F) : ℂ :=
  ((c₁ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2)

omit [MeasurableSpace F] [BorelSpace F] in
theorem cst_mul (c₁ : Fˣ →* ℂˣ) (g h : GL (Fin 2) F) : cst c₁ (g * h) = cst c₁ g * cst c₁ h := by
  simp only [cst, map_mul, Units.val_mul, mp, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  ring

omit [MeasurableSpace F] [BorelSpace F] in

theorem sbe_shift {A : F} (hA : A ≠ 0) {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) :
    (fun y : F × F => Φ (y * (A, 1))) ∈ SBE (F × F) := by
  let H : (F × F) ≃ₜ (F × F) := (Homeomorph.mulRight₀ A hA).prodCongr (Homeomorph.refl F)
  have e : (fun y : F × F => Φ (y * (A, 1))) = Φ ∘ H := by
    funext y
    have : y * ((A, 1) : F × F) = H y := by ext <;> simp [H]
    simp only [Function.comp, this]
  rw [e]
  exact ⟨hΦ.1.comp_continuous H.continuous, hΦ.2.comp_homeomorph H⟩

theorem piS_eq (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (h : GL (Fin 2) F) (Φ : F × F → ℂ) :
    piS χ c₁ h Φ = fun x => cst c₁ h * rWS χ (one1 h) (fun y => Φ (y * ((h.val).det, 1))) x :=
  rfl

theorem piS_mem [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (c₁ : Fˣ →* ℂˣ)
    {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) (h : GL (Fin 2) F) : piS χ c₁ h Φ ∈ SBE (F × F) := by
  rw [piS_eq]
  exact sbe_const_mul _
    ((good_all hχ hχ1 (det_normalized_determinant_one h)).2 1 Matrix.det_one _ (sbe_shift (det_ne h) hΦ)).1

theorem piS_mul [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (c₁ : Fˣ →* ℂˣ)
    {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) (g h : GL (Fin 2) F) :
    piS χ c₁ (g * h) Φ = piS χ c₁ g (piS χ c₁ h Φ) := by
  have hA := det_ne g
  have hB := det_ne h
  have hΨ := sbe_shift (mul_ne_zero hA hB) hΦ
  have step : (fun y => piS χ c₁ h Φ (y * ((g.val).det, 1))) = fun y => cst c₁ h *
      rWS χ (cjA (g.val).det (one1 h)) (fun v => Φ (v * ((g.val).det * (h.val).det, 1))) y := by
    funext y
    rw [piS_eq]
    simp only []
    rw [dil χ (det_normalized_determinant_one h) hA]
    congr 2
    funext v
    have e : (((g.val).det, 1) : F × F) * ((h.val).det, 1) = ((g.val).det * (h.val).det, 1) := by
      ext <;> simp
    rw [mul_assoc, e]
  rw [piS_eq χ c₁ (g * h), piS_eq χ c₁ g, step, rWS_const, normalized_determinant_cocycle, det_mul',
    ((good_all hχ hχ1 (cjA_det (det_normalized_determinant_one h) hA)).2 _ (det_normalized_determinant_one g) _ hΨ).2, cst_mul]
  funext x
  ring

theorem wcS_eq (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Φ : F × F → ℂ) (g : GL (Fin 2) F) :
    WcS χ c₁ c₂ Φ g = ∫ u : Fˣ, piS χ c₁ g Φ ((u : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) *
      (((c₂ u)⁻¹ : ℂˣ) : ℂ) ∂multHaar F := by
  simp only [WcS, piS]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  ring

theorem sPiRep : SPiRep := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 c₁ c₂ _ _ Φ hΦ g h
  refine ⟨?_, piS_mem hχ hχ1 c₁ hΦ h⟩
  rw [wcS_eq, wcS_eq, piS_mul hχ hχ1 c₁ hΦ g h]

end GlobalTheory.CompanionTheory.SplitPi
