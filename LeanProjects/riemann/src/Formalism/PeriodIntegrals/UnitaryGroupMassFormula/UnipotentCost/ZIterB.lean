import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ZIterA

open scoped ContDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.ZI

variable (s : ℕ)

abbrev En : Type := (Fin s → ℂ) →L[ℝ] (Fin s → ℂ)

def act (Z : Fin s → Fin s → ℂ) : En s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (Matrix.of Z).mulVec v
      map_add' := fun v w => Matrix.mulVec_add _ _ _
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }

theorem act_apply (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : act s Z v = (Matrix.of Z).mulVec v := rfl

def eA : (Fin s → Fin s → ℂ) →L[ℝ] En s :=
  LinearMap.toContinuousLinearMap
    { toFun := act s
      map_add' := fun Z Z' => by
        ext1 v
        simp only [act_apply, ContinuousLinearMap.add_apply]
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c Z => by
        ext1 v
        simp only [act_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        exact Matrix.smul_mulVec c (Matrix.of Z) v }

theorem eA_apply (Z : Fin s → Fin s → ℂ) (v : Fin s → ℂ) : eA s Z v = (Matrix.of Z).mulVec v := rfl

def invF (Z : Fin s → Fin s → ℂ) : Fin s → Fin s → ℂ := Matrix.of.symm (Matrix.of Z)⁻¹

theorem eA_mul_inv {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    eA s Z * eA s (invF s Z) = 1 ∧ eA s (invF s Z) * eA s Z = 1 := by
  have hu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr h
  have hinv : Matrix.of (invF s Z) = (Matrix.of Z)⁻¹ := by simp [invF]
  constructor <;> ext1 v <;>
    simp only [ContinuousLinearMap.mul_apply, eA_apply, ContinuousLinearMap.one_apply,
      Matrix.mulVec_mulVec, hinv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
      Matrix.one_mulVec]

theorem isUnit_eA {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) : IsUnit (eA s Z) :=
  ⟨⟨eA s Z, eA s (invF s Z), (eA_mul_inv s h).1, (eA_mul_inv s h).2⟩, rfl⟩

theorem inverse_eA {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    Ring.inverse (eA s Z) = eA s (invF s Z) := by
  exact Ring.inverse_unit ⟨eA s Z, eA s (invF s Z), (eA_mul_inv s h).1, (eA_mul_inv s h).2⟩

def lamL (a b : Fin s) (ε : Bool) (T : En s) : (Fin s → Fin s → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun W => if ε then (T (fun c => W c b) a).re else (T (fun c => W c b) a).im
      map_add' := fun W W' => by
        have : (fun c => (W + W') c b) = (fun c => W c b) + (fun c => W' c b) := rfl
        rw [this, map_add]
        cases ε <;> simp
      map_smul' := fun r W => by
        have : (fun c => (r • W) c b) = r • (fun c => W c b) := rfl
        rw [this, map_smul]
        cases ε <;> simp }

theorem lamL_apply (a b : Fin s) (ε : Bool) (T : En s) (W : Fin s → Fin s → ℂ) :
    lamL s a b ε T W = if ε then (T (fun c => W c b) a).re else (T (fun c => W c b) a).im := rfl

def lamF (i : Fin s × Fin s × Bool) : En s →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => lamL s i.1 i.2.1 i.2.2 T
      map_add' := fun T T' => by
        ext W; simp only [lamL_apply, ContinuousLinearMap.add_apply]
        cases i.2.2 <;> simp
      map_smul' := fun c T => by
        ext W; simp only [lamL_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply]
        cases i.2.2 <;> simp }

def cF (i : Fin s × Fin s × Bool) (Z : Fin s → Fin s → ℂ) : (Fin s → Fin s → ℂ) →L[ℝ] ℝ :=
  lamF s i (Ring.inverse (eA s Z))

theorem cF_apply (i : Fin s × Fin s × Bool) {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0)
    (W : Fin s → Fin s → ℂ) :
    cF s i Z W = if i.2.2 then (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).re
      else (((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1).im := by
  have hinv : Matrix.of (invF s Z) = (Matrix.of Z)⁻¹ := by simp [invF]
  rw [cF, inverse_eA s h]
  show lamL s i.1 i.2.1 i.2.2 (eA s (invF s Z)) W = _
  rw [lamL_apply, eA_apply, hinv]
  have e : ((Matrix.of Z)⁻¹.mulVec fun c => W c i.2.1) i.1
      = ((Matrix.of Z)⁻¹ * Matrix.of W) i.1 i.2.1 := by
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
  rw [e]

theorem isOpen_det : IsOpen {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det (by exact continuous_id)) continuous_const

theorem contDiffOn_cF (i : Fin s × Fin s × Bool) (n : ℕ) :
    ContDiffOn ℝ n (cF s i) {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} := by
  have hinv : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x | IsUnit x} := fun x hx => by
    obtain ⟨u, rfl⟩ := hx
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt
  exact (lamF s i).contDiff.comp_contDiffOn
    (hinv.comp (eA s).contDiff.contDiffOn (fun Z hZ => isUnit_eA s hZ))

theorem contDiffOn_inv (n : ℕ) : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x : En s | IsUnit x} :=
  fun x hx => by
    obtain ⟨u, rfl⟩ := hx
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt

theorem norm_inverse_le {Z : Fin s → Fin s → ℂ} (h : (Matrix.of Z).det ≠ 0) :
    ‖Ring.inverse (eA s Z)‖ ≤ ‖eA s‖ * ‖invF s Z‖ := by
  rw [inverse_eA s h]
  exact (eA s).le_opNorm _

theorem cF_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : Fin s → Fin s → ℂ, (Matrix.of Z).det ≠ 0 → ∀ i, ∀ a ≤ n,
    ‖iteratedFDeriv ℝ a (cF s i) Z‖ ≤ K * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by
  set U := {Z : Fin s → Fin s → ℂ | (Matrix.of Z).det ≠ 0} with hU_def
  have hUo : IsOpen U := isOpen_det s
  let φ : (Fin s → Fin s → ℂ) → En s := fun Z => Ring.inverse (eA s Z)
  let P : (En s →L[ℝ] En s) →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] En s) :=
    (ContinuousLinearMap.compL ℝ (Fin s → Fin s → ℂ) (En s) (En s)).flip (eA s)
  let Bi : En s →L[ℝ] En s →L[ℝ] ((Fin s → Fin s → ℂ) →L[ℝ] En s) :=
    (ContinuousLinearMap.compL ℝ (En s) (En s →L[ℝ] En s) _ (-P)).comp
      (ContinuousLinearMap.mulLeftRight ℝ (En s))
  have hφ : ∀ m : ℕ, ContDiffOn ℝ m φ U := fun m =>
    (contDiffOn_inv s m).comp (eA s).contDiff.contDiffOn (fun Z hZ => isUnit_eA s hZ)
  have hd : ∀ Z ∈ U, fderiv ℝ φ Z = Bi (φ Z) (φ Z) := by
    intro Z hZ
    obtain ⟨u, hu⟩ := isUnit_eA s hZ
    have h0 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hu] at h0
    have h1 := h0.comp Z (eA s).hasFDerivAt
    have hinv : ((u⁻¹ : (En s)ˣ) : En s) = φ Z := by
      show _ = Ring.inverse (eA s Z)
      rw [← hu, Ring.inverse_unit u]
    rw [show φ = Ring.inverse ∘ (eA s) from rfl, h1.fderiv, hinv]
    ext W : 1
    simp [Bi, P, φ]
  obtain ⟨K0, hK0, hb⟩ := quad_bound Bi hUo hφ hd n
  refine ⟨(∑ j, ‖lamF s j‖) * K0,
    mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hK0, ?_⟩
  intro Z hZ i a ha
  have hZU : Z ∈ U := hZ
  have hcf : cF s i = (lamF s i) ∘ φ := rfl
  have e1 : iteratedFDeriv ℝ a (cF s i) Z = iteratedFDerivWithin ℝ a (cF s i) U Z :=
    (iteratedFDerivWithin_of_isOpen a hUo hZU).symm
  have e2 : iteratedFDeriv ℝ a φ Z = iteratedFDerivWithin ℝ a φ U Z :=
    (iteratedFDerivWithin_of_isOpen a hUo hZU).symm
  have h3 : ‖iteratedFDerivWithin ℝ a (cF s i) U Z‖
      ≤ ‖lamF s i‖ * ‖iteratedFDerivWithin ℝ a φ U Z‖ := by
    rw [hcf]
    exact (lamF s i).norm_iteratedFDerivWithin_comp_left (hφ a Z hZU) hUo.uniqueDiffOn hZU le_rfl
  have hLi : ‖lamF s i‖ ≤ ∑ j, ‖lamF s j‖ :=
    Finset.single_le_sum (f := fun j => ‖lamF s j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hM0 : 0 ≤ max 1 ‖φ Z‖ := le_trans zero_le_one (le_max_left _ _)
  have hM : max 1 ‖φ Z‖ ≤ max 1 ‖eA s‖ * max 1 ‖φ Z‖ :=
    le_mul_of_one_le_left hM0 (le_max_left _ _)
  have hL0 : 0 ≤ ∑ j, ‖lamF s j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [e1]
  calc _ ≤ ‖lamF s i‖ * ‖iteratedFDerivWithin ℝ a φ U Z‖ := h3
    _ ≤ (∑ j, ‖lamF s j‖) * (K0 * max 1 ‖φ Z‖ ^ (a + 1)) := by
        rw [← e2]
        exact mul_le_mul hLi (hb Z hZU a ha) (norm_nonneg _) hL0
    _ ≤ (∑ j, ‖lamF s j‖) * (K0 * (max 1 ‖eA s‖ * max 1 ‖φ Z‖) ^ (a + 1)) := by
        gcongr
    _ = (∑ j, ‖lamF s j‖) * K0 * (max 1 ‖eA s‖ * max 1 ‖Ring.inverse (eA s Z)‖) ^ (a + 1) := by
        ring

end PI.UnitaryGroupMassFormula.UsCost.ZI
