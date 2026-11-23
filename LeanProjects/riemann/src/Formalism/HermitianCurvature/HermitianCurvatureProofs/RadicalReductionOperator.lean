import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionUnitary

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.RadicalReductionOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

def MxOp (k r : ℕ) : Type := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

instance (k r : ℕ) : NormedRing (MxOp k r) := Matrix.linftyOpNormedRing

instance (k r : ℕ) : NormedAlgebra ℂ (MxOp k r) := Matrix.linftyOpNormedAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def toOp (k r : ℕ) : Q.Mx k r ≃ₗ[ℝ] MxOp k r where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by
    change (c • x : Q.Mx k r) = (c • (@id (MxOp k r) x))
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c x, RCLike.real_smul_eq_coe_smul (K := ℂ) c (@id (MxOp k r) x)]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem locLog : NFRadRedR.LocLog := by
  intro k r z _ _
  obtain ⟨O, hO, h1, Λ, hΛ, hΛg⟩ := RadicalReductionUnitary.locLogOp (k := k) (r := r) z
  have hΛ' : ContDiffOn ℝ ∞ (fun x : MxOp k r => @id (MxOp k r) (Λ x)) (@id (Set (MxOp k r)) O) := hΛ
  have hO' : IsOpen (O : Set (Q.Mx k r)) := hO
  refine ⟨O, hO', h1, Λ, ?_, hΛg⟩
  have hL1 := (toOp k r).toContinuousLinearEquiv.toContinuousLinearMap.contDiff (n := ∞)
  have hL2 := (toOp k r).toContinuousLinearEquiv.symm.toContinuousLinearMap.contDiff (n := ∞)
  have h := hL2.comp_contDiffOn (hΛ'.comp (s := (O : Set (Q.Mx k r))) hL1.contDiffOn (fun x hx => hx))
  exact h.congr (fun x _ => rfl)

end Formalism.FourierDecayAlt.P.RadicalReductionOperator

namespace Formalism.FourierDecayAlt.P

theorem local_logarithm_unitary : NFRadRedR.LocLog := RadicalReductionOperator.locLog

end Formalism.FourierDecayAlt.P
