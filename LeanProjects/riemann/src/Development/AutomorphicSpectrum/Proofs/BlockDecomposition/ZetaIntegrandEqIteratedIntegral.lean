import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Th
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mp_add (a : Fˣ) (s t : ℂ) : mp a (s + t) = mp a s * mp a t := by
  have hm : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 := by
    have := modulus_ne_zero a.ne_zero
    exact_mod_cast this
  exact Complex.cpow_add _ _ hm

omit [MeasurableSpace F] [BorelSpace F] in
theorem mp_mul (a b : Fˣ) (s : ℂ) : mp (a * b) s = mp a s * mp b s := by
  simp only [mp, Units.val_mul, modulus_mul]
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) s

omit [MeasurableSpace F] [BorelSpace F] in
theorem mp_inv (a : Fˣ) (s : ℂ) : mp a⁻¹ s = mp a (-s) := by
  have h0 : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
  simp only [mp, Units.val_inv_eq_inv_val, modulus_inv]
  push_cast
  rw [Complex.cpow_neg, Complex.inv_cpow]
  rw [Complex.arg_ofReal_of_nonneg h0.le]
  exact Real.pi_pos.ne

omit [MeasurableSpace F] [BorelSpace F] in
theorem modulus_det_integral_GL2_eq_one {k : GL (Fin 2) F} (hk : k ∈ K2 F) (z : ℂ) :
    mp (GeneralLinearGroup.det k) z = 1 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have d1 : (k.val).det ∈ 𝒪[F] := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h1 0 0) (h1 1 1)) (mul_mem (h1 0 1) (h1 1 0))
  have d2 : ((k⁻¹).val).det ∈ 𝒪[F] := by
    rw [Matrix.det_fin_two]
    exact sub_mem (mul_mem (h2 0 0) (h2 1 1)) (mul_mem (h2 0 1) (h2 1 0))
  have m1 : modulus (k.val).det ≤ 1 := modulus_le_one_iff.2 d1
  have m2 : modulus ((k⁻¹).val).det ≤ 1 := modulus_le_one_iff.2 d2
  have e : modulus (k.val).det * modulus ((k⁻¹).val).det = 1 := by
    rw [← modulus_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
    simp [modulus_one]
  have hm : modulus (k.val).det = 1 := by
    refine le_antisymm m1 ?_
    calc (1 : NNReal) = modulus (k.val).det * modulus ((k⁻¹).val).det := e.symm
      _ ≤ modulus (k.val).det * 1 := mul_le_mul_of_nonneg_left m2 zero_le
      _ = modulus (k.val).det := mul_one _
  simp [mp, Matrix.GeneralLinearGroup.val_det_apply, hm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem det_diagonal_two (a b : Fˣ) : GeneralLinearGroup.det (dg2 a b) = a * b := by
  ext
  simp [dg2, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem det_unipotent_adele (x : F) : GeneralLinearGroup.det (uni2 x) = 1 := by
  ext
  simp [uni2, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem diag_inv_mul_alt (t : Fˣ) : dg2 t⁻¹ 1 * dg2 t 1 = (1 : GL (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem first_vector_diag_unipotent_mul (t : Fˣ) (x : F) (h : GL (Fin 2) F) :
    e1r (dg2 t 1 * (uni2 x * h)) = ![(t : F), t * x] ᵥ* (h : Matrix (Fin 2) (Fin 2) F) := by
  ext i
  fin_cases i <;>
    simp [e1r, dg2, uni2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem second_vector_diag_unipotent_invariant (t : Fˣ) (x : F) (h : GL (Fin 2) F) :
    e2r (dg2 t 1 * (uni2 x * h)) = e2r h := by
  ext i
  fin_cases i <;> simp [e2r, dg2, uni2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

omit [MeasurableSpace F] [BorelSpace F] in
theorem mp_det_hI (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ K2 F) (z : ℂ) :
    mp (GeneralLinearGroup.det (hI p)) z = mp p.1 z * mp p.2.1 (2 * z) := by
  rw [hI, map_mul, det_diagonal_two, mp_mul, modulus_det_integral_GL2_eq_one hp, mp_mul, mp_mul, two_mul, mp_add]
  ring

omit [MeasurableSpace F] [BorelSpace F] in
theorem weight (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ K2 F) (t : Fˣ) (s : ℂ) :
    ((wR p : ℝ) : ℂ) * mp (t * GeneralLinearGroup.det (hI p)) (s + 1 / 2) * mp t⁻¹ (s - 1 / 2) =
      mp (GeneralLinearGroup.det (hI p)) (1 / 2) * mp t 1 * mp p.1 (s - 1) * mp p.2.1 (2 * s) := by
  have hw : ((wR p : ℝ) : ℂ) = mp p.1 (-1) := by
    rw [wR, mp, Complex.cpow_neg_one]
    push_cast
    rfl
  have ea : mp p.1 (1 / 2) * mp p.1 (s - 1) = mp p.1 (-1) * mp p.1 (s + 1 / 2) := by
    rw [← mp_add, ← mp_add]; congr 1; ring
  have eb : mp p.2.1 (2 * (1 / 2)) * mp p.2.1 (2 * s) = mp p.2.1 (2 * (s + 1 / 2)) := by
    rw [← mp_add]; congr 1; ring
  have et : mp t (s + 1 / 2) * mp t (-(s - 1 / 2)) = mp t 1 := by
    rw [← mp_add]; congr 1; ring
  rw [hw, mp_mul, mp_inv, mp_det_hI p hp, mp_det_hI p hp, ← eb, ← et]
  linear_combination (-(mp p.2.1 (2 * (1 / 2)) * mp p.2.1 (2 * s) * mp t (s + 1 / 2) * mp t (-(s - 1 / 2)))) * ea

theorem pointwise (ψ : AddChar F Circle) (ν' : Fˣ →* ℂˣ) (φ₀ φ : (Fin 2 → F) → ℂ)
    (V : GL (Fin 2) F → ℂ) (s : ℂ)
    (hV : ∀ x g, V (uni2 x * g) = ((ψ⁻¹ x : Circle) : ℂ) * V g)
    (p : Fˣ × Fˣ × GL (Fin 2) F) (hp : p.2.2 ∈ K2 F) (t : Fˣ) (x : F) :
    ((wR p : ℝ) : ℂ) * (Jm φ₀ φ V ν' s ∘ Th) (t, uni2 x * hI p) =
      (((ν'⁻¹ (GeneralLinearGroup.det (hI p)) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det (hI p)) (1 / 2) *
          V (hI p) * φ (e2r (hI p)) * mp p.1 (s - 1) * mp p.2.1 (2 * s)) *
        ((((ν' t)⁻¹ * ν'⁻¹ t : ℂˣ) : ℂ) * mp t 1 *
          (φ₀ (![(t : F), t * x] ᵥ* (hI p : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ))) := by
  have hw := weight p hp t s
  have hu : ((((ν' (t * GeneralLinearGroup.det (hI p)))⁻¹ : ℂˣ) : ℂ)) * ((ν' t⁻¹ : ℂˣ) : ℂ) =
      ((ν'⁻¹ (GeneralLinearGroup.det (hI p)) : ℂˣ) : ℂ) * (((ν' t)⁻¹ * ν'⁻¹ t : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    simp only [map_mul, map_inv, MonoidHom.inv_apply, mul_inv]
    rw [mul_assoc, mul_left_comm]
  have hV' : V (dg2 t⁻¹ 1 * (dg2 t 1 * (uni2 x * hI p))) = (ψ (-x) : ℂ) * V (hI p) := by
    rw [← mul_assoc, diag_inv_mul_alt, one_mul, hV, AddChar.inv_apply]
  have hd : GeneralLinearGroup.det (dg2 t 1 * (uni2 x * hI p)) = t * GeneralLinearGroup.det (hI p) := by
    rw [map_mul, map_mul, det_diagonal_two, det_unipotent_adele, one_mul, mul_one]
  simp only [Function.comp_apply, Th, Jm]
  rw [hV', first_vector_diag_unipotent_mul, second_vector_diag_unipotent_invariant, hd]
  linear_combination
    (((ν' (t * GeneralLinearGroup.det (hI p)))⁻¹ : ℂˣ) : ℂ) * ((ν' t⁻¹ : ℂˣ) : ℂ) *
      φ₀ (![(t : F), t * x] ᵥ* (hI p : Matrix (Fin 2) (Fin 2) F)) * φ (e2r (hI p)) *
      (ψ (-x) : ℂ) * V (hI p) * hw +
    (mp (GeneralLinearGroup.det (hI p)) (1 / 2) * mp t 1 * mp p.1 (s - 1) * mp p.2.1 (2 * s)) *
      φ₀ (![(t : F), t * x] ᵥ* (hI p : Matrix (Fin 2) (Fin 2) F)) * φ (e2r (hI p)) *
      (ψ (-x) : ℂ) * V (hI p) * hu

end

theorem main : ForS fun F _ _ _ _ _ _ ψ => ∀ (ν' : Fˣ →* ℂˣ) (φ₀ φ : (Fin 2 → F) → ℂ) (V : GL (Fin 2) F → ℂ) (s : ℂ),
    (∀ x g, V (uni2 x * g) = ((ψ⁻¹ x : Circle) : ℂ) * V g) →
    ∀ p : Fˣ × Fˣ × GL (Fin 2) F, p.2.2 ∈ K2 F →
      z2I (W2 ψ ν' ν'⁻¹ φ₀) V φ s p =
        ∫ t : Fˣ, ∫ x, (wR p : ℂ) * (Jm φ₀ φ V ν' s ∘ Th) (t, uni2 x * hI p) ∂selfDualMeasure ψ ∂multHaar F := by
  intro F _ _ _ _ _ _ ψ _ ν' φ₀ φ V s hV p hp
  simp_rw [pointwise ψ ν' φ₀ φ V s hV p hp, integral_const_mul]
  simp only [z2I, W2]
  ring

end GlobalTheory.CompanionTheory.DampedZetaMajorant.Iter
