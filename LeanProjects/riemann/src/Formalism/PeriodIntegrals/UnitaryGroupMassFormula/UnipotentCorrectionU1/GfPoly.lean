import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.GfPolyA

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PolynomialDegreeClosure in
theorem generating_function_polynomial : GfPoly := by
  intro k r z z'
  have hD : ∀ l : Fin (r + 2), IsPolyDeg l.val (fun g : B.Mat k r => Dmin k r z z' g l) := fun l =>
    pd_det l.val (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt))) fun i j =>
      pd_herm (Hpk k r) (fvec k r z' (Fin.castLE (Nat.le_of_lt_succ l.isLt) j))
        (fvec k r z (Fin.castLE (Nat.le_of_lt_succ l.isLt) i))
  have hDs : ∀ l : Fin (r + 2), IsPolyDeg l.val (fun g : B.Mat k r => star (Dmin k r z z' g l)) := fun l =>
    pd_det_star l.val (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
      (Fin.castLE (Nat.le_of_lt_succ l.isLt))) fun i j =>
      pd_herm_star (Hpk k r) (fvec k r z' (Fin.castLE (Nat.le_of_lt_succ l.isLt) j))
        (fvec k r z (Fin.castLE (Nat.le_of_lt_succ l.isLt) i))
  have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) = fun g =>
      Dmin k r z z' g (Fin.last (r + 1)) * star (Dmin k r z z' g (Fin.last (r + 1))) -
      ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
        (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩)) := by
    funext g
    simp only [Gf]
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    rfl
  rw [e]
  refine pd_sub (pd_mono ?_ (pd_mul (hD _) (hDs _))) (pd_mono ?_ (pd_cmul _ (pd_mul (hD _) (hDs _))))
  · omega
  · omega

end PI.UnitaryCorollaryDerivatives
