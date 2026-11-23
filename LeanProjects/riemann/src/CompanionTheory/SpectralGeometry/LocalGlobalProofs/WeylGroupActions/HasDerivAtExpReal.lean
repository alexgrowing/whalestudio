import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
import CompanionTheory.HarishChandraModules.NonemptyRepresentations.ExpEntry

open Matrix Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.HolCoef

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def cone : Set (B.Mat 4 0) := {g | g 4 4 ≠ 0}

def IsHolHom {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (K : ℕ) (f : B.Mat 4 0 → E) : Prop :=
  AnalyticOnNhd ℂ f cone ∧ ∀ t : ℂ, t ≠ 0 → ∀ g ∈ cone, f (t • g) = (t ^ K)⁻¹ • f g

def minor2 (g : B.Mat 4 0) : ℂ := (g.submatrix ![3, 4] ![3, 4]).det

def minor3 (g : B.Mat 4 0) : ℂ := (g.submatrix ![2, 3, 4] ![2, 3, 4]).det

def minor4 (g : B.Mat 4 0) : ℂ := (g.submatrix ![1, 2, 3, 4] ![1, 2, 3, 4]).det

def coef (p N : ℕ) (g : B.Mat 4 0) : ℂ := (g 4 4 ^ N)⁻¹ * (minor2 g ^ p * minor3 g ^ p * minor4 g)

def wt (p N : ℕ) : Fin (2 * 0 + 4 + 1) → ℂ := ![0, 1, (p : ℂ) + 1, 2 * (p : ℂ) + 1, 2 * (p : ℂ) + 1 - N]

def eul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b c d : Fin (2 * 0 + 4 + 1)) (f : B.Mat 4 0 → E) :
    B.Mat 4 0 → E := fun g => g c d • fderiv ℂ f g (Matrix.single a b 1)

theorem isOpen_cone : IsOpen cone :=
  isOpen_ne_fun ((continuous_apply (4 : Fin (2 * 0 + 4 + 1))).comp (continuous_apply (4 : Fin (2 * 0 + 4 + 1)))) continuous_const

theorem coef_one (p N : ℕ) : coef p N 1 = 1 := by
  have h2 : minor2 1 = 1 := by
    unfold minor2; rw [Matrix.submatrix_one _ (by decide), det_one]
  have h3 : minor3 1 = 1 := by
    unfold minor3; rw [Matrix.submatrix_one _ (by decide), det_one]
  have h4 : minor4 1 = 1 := by
    unfold minor4; rw [Matrix.submatrix_one _ (by decide), det_one]
  simp [coef, h2, h3, h4]

section deriv

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_exp_real (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => CompanionTheory.D.Inhab.exp_entry n X i j

theorem rdV_eq_fderiv (X g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : DifferentiableAt ℂ f g) : RdV X f g = fderiv ℂ f g (g * X) := by
  unfold RdV
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ := (LinearMap.mulLeft ℝ g).toContinuousLinearMap
  have h1 : HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_real X)
  have h2 : HasFDerivAt f ((fderiv ℂ f g).restrictScalars ℝ) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
    rw [Matrix.mul_one]
    exact hf.hasFDerivAt.restrictScalars ℝ
  exact (h2.comp_hasDerivAt (0 : ℝ) h1).deriv

theorem ldV_eq_fderiv {k r : ℕ} (X g : B.Mat k r) (f : B.Mat k r → E)
    (hf : DifferentiableAt ℂ f g) : B.LdV X f g = fderiv ℂ f g (-(X * g)) := by
  unfold B.LdV
  let L : B.Mat k r →L[ℝ] B.Mat k r := (LinearMap.mulRight ℝ g).toContinuousLinearMap
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • (-X)) * g) ((-X) * g) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_real (-X))
  have h2 : HasFDerivAt f ((fderiv ℂ f g).restrictScalars ℝ) (NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)) * g) := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
    rw [Matrix.one_mul]
    exact hf.hasFDerivAt.restrictScalars ℝ
  have h3 := (h2.comp_hasDerivAt (0 : ℝ) h1).deriv
  simp only [smul_neg, Matrix.neg_mul] at h3
  exact h3

theorem eabH_eq_fderiv (H g : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : DifferentiableAt ℂ f g) : EabH H a b f g = fderiv ℂ f g (g * Matrix.single a b 1) := by
  unfold EabH
  rw [rdV_eq_fderiv _ _ _ hf, rdV_eq_fderiv _ _ _ hf, ← map_smul, ← map_add, ← Matrix.mul_smul, ← Matrix.mul_add]
  congr 2
  unfold hpart1 hpart2
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [this, ← smul_add]
  rw [sub_add_add_cancel, ← two_smul ℂ, smul_smul]
  norm_num

end deriv

end GlobalTheory.CompanionTheory.HolCoef
