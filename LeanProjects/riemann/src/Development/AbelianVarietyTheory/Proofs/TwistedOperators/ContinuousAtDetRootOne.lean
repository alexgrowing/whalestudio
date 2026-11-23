import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocal

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar unitScalar)

noncomputable section

namespace GlobalTheory.ExtCharCont

open GlobalTheory.ExtChar Polynomial

theorem charpoly_smul_comp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {c : ℂ} (hc : c ≠ 0) :
    (c • M).charpoly = C (c ^ n) * M.charpoly.comp (C c⁻¹ * X) := by
  apply Polynomial.funext
  intro t
  rw [eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, Matrix.eval_charpoly, Matrix.eval_charpoly]
  have h := Matrix.det_smul (Matrix.scalar (Fin n) (c⁻¹ * t) - M) c
  rw [Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext i j
  simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]
  split_ifs <;> field_simp

theorem isRegSS_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {c : ℂ} (hc : c ≠ 0) (h : IsRegSS M) :
    IsRegSS (c • M) := by
  unfold IsRegSS at *
  obtain ⟨a, b, hab⟩ := h
  rw [charpoly_smul_comp M hc]
  have h1 := congrArg (fun p : ℂ[X] => p.comp (C c⁻¹ * X)) hab
  simp only [add_comp, mul_comp, one_comp] at h1
  refine ⟨C (c ^ n)⁻¹ * a.comp (C c⁻¹ * X), C (c ^ n)⁻¹ * C c * b.comp (C c⁻¹ * X), ?_⟩
  have e1 : (C (c ^ n)⁻¹ * C (c ^ n) : ℂ[X]) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hc), C_1]
  have e2 : (C c * C c⁻¹ : ℂ[X]) = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hc, C_1]
  rw [derivative_C_mul, derivative_comp, derivative_C_mul, derivative_X, mul_one]
  linear_combination h1 + (a.comp (C c⁻¹ * X) * M.charpoly.comp (C c⁻¹ * X) +
    C c * C c⁻¹ * b.comp (C c⁻¹ * X) * (derivative M.charpoly).comp (C c⁻¹ * X)) * e1 +
    b.comp (C c⁻¹ * X) * (derivative M.charpoly).comp (C c⁻¹ * X) * e2

variable {n : ℕ} (ε : Fin n → Bool)

theorem umat_mul' (a b : UJ ε) : umat (a * b) = umat a * umat b := rfl

theorem continuousAt_detRoot_one : ContinuousAt (detRoot ε) 1 := by
  have h1 : Continuous fun g : UJ ε => (umat g).det :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_det
  have h2 : (umat (1 : UJ ε)).det ∈ Complex.slitPlane := by
    have : umat (1 : UJ ε) = 1 := rfl
    rw [this, Matrix.det_one]
    exact Complex.one_mem_slitPlane
  have h3 : ContinuousAt (fun g : UJ ε => Complex.arg (umat g).det) 1 :=
    ContinuousAt.comp (f := fun g : UJ ε => (umat g).det) (Complex.continuousAt_arg h2) h1.continuousAt
  exact Circle.exp.continuous.continuousAt.comp (h3.div_const _)

def locRoot (s y : UJ ε) : Circle := detRoot ε s * detRoot ε (s⁻¹ * y)

theorem continuousAt_locRoot (s : UJ ε) : ContinuousAt (locRoot ε s) s := by
  have h : ContinuousAt (fun y : UJ ε => detRoot ε (s⁻¹ * y)) s := by
    exact (continuousAt_detRoot_one ε).comp_of_eq ((continuous_const.mul continuous_id).continuousAt (x := s))
      (inv_mul_cancel s)
  exact continuousAt_const.mul h

variable [NeZero n]

theorem locRoot_pow (s y : UJ ε) : ((locRoot ε s y : Circle) : ℂ) ^ n = (umat y).det := by
  rw [locRoot, Circle.coe_mul, mul_pow, detRoot_pow ε (NeZero.ne n), detRoot_pow ε (NeZero.ne n),
    ← Matrix.det_mul, ← umat_mul', mul_inv_cancel_left]

def locPart (s y : UJ ε) : SUJ ε :=
  ⟨unitScalar ε (locRoot ε s y)⁻¹ * y, by
    show (umat (unitScalar ε (locRoot ε s y)⁻¹ * y)).det = 1
    rw [det_unitScalar_mul, Circle.coe_inv, inv_pow, locRoot_pow, inv_mul_cancel₀]
    intro h0
    have := GlobalTheory.SqIntSU.norm_det_umat ε y
    rw [h0, norm_zero] at this
    exact zero_ne_one this⟩

theorem continuousAt_locPart (s : UJ ε) : ContinuousAt (locPart ε s) s := by
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
  show ContinuousAt (fun y => unitScalar ε (locRoot ε s y)⁻¹ * y) s
  exact ((GlobalTheory.SqIntSU.continuous_unitScalar ε).continuousAt.comp (continuousAt_locRoot ε s).inv).mul continuousAt_id

theorem scalarMul_loc (s y : UJ ε) : scalarMul ε (locRoot ε s y, locPart ε s y) = y := by
  show unitScalar ε (locRoot ε s y) * (unitScalar ε (locRoot ε s y)⁻¹ * y) = y
  rw [← unitScalar_inv, mul_inv_cancel_left]

theorem isRegSS_unitScalar_mul (z : Circle) (y : UJ ε) (h : IsRegSS (ujMat ε y)) :
    IsRegSS (ujMat ε (unitScalar ε z * y)) := by
  have e : ujMat ε (unitScalar ε z * y) = (z : ℂ) • ujMat ε y := by
    show (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * ujMat ε y = _
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [e]
  exact isRegSS_smul _ (Circle.coe_ne_zero z) h

theorem continuousAt_avgChar (m : ℤ) (Θ' : SUJ ε → ℂ)
    (hΘ : ∀ g : SUJ ε, IsRegSS (suMat ε g) → ContinuousAt Θ' g) (g : SUJ ε) (hg : IsRegSS (suMat ε g)) :
    ContinuousAt (avgChar ε m Θ') g := by
  unfold avgChar
  refine continuousAt_const.mul (tendsto_finset_sum _ fun j _ => ?_)
  have h : ContinuousAt (fun x : SUJ ε => Θ' (cen ε j * x)) g :=
    ContinuousAt.comp (f := fun x : SUJ ε => cen ε j * x)
      (hΘ _ (isRegSS_unitScalar_mul ε (ZMod.toCircle j)⁻¹ (g : UJ ε) hg))
      (continuous_const.mul continuous_id).continuousAt
  exact continuousAt_const.mul h

theorem continuousAt_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (m : ℤ) (Θ' : SUJ ε → ℂ), (∀ g : SUJ ε, IsRegSS (suMat ε g) → ContinuousAt Θ' g) → ∀ s : UJ ε, IsRegSS (ujMat ε s) → ContinuousAt (GlobalTheory.ExtChar.extChar ε m Θ') s := by
  intro n _ ε m Θ' hΘ s hs
  have e : extChar ε m Θ' = fun y => ((locRoot ε s y : Circle) : ℂ) ^ m * avgChar ε m Θ' (locPart ε s y) := by
    funext y
    rw [← extChar_scalarMul, scalarMul_loc]
  rw [e]
  have h1 : ContinuousAt (fun y => ((locRoot ε s y : Circle) : ℂ)) s :=
    continuous_subtype_val.continuousAt.comp (continuousAt_locRoot ε s)
  refine (h1.zpow₀ m (Or.inl (Circle.coe_ne_zero _))).mul ?_
  exact ContinuousAt.comp (f := locPart ε s)
    (continuousAt_avgChar ε m Θ' hΘ _ (isRegSS_unitScalar_mul ε (locRoot ε s s)⁻¹ s hs))
    (continuousAt_locPart ε s)

end GlobalTheory.ExtCharCont

end
