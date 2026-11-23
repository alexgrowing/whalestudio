import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPhaseCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRDatumConst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.TwoByOneBlock

section cWLemmas

variable {k r : ℕ}

theorem cW_mul (θ θ' : ℝ) : cW k r θ * cW k r θ' = cW k r (θ + θ') := by
  unfold cW
  rw [← emb_mul, smul_mul_smul_comm, mul_one, ← Complex.exp_add]
  congr 3
  push_cast
  ring

theorem cW_zero : cW k r 0 = 1 := by
  unfold cW
  simp [emb_one]

theorem cW_inv (θ : ℝ) : (cW k r θ)⁻¹ = cW k r (-θ) := by
  apply Matrix.inv_eq_right_inv
  rw [cW_mul, add_neg_cancel, cW_zero]

theorem cW_mulVec (θ : ℝ) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    cW k r θ *ᵥ v = Complex.exp ((θ : ℂ) * Complex.I) • v := by
  unfold cW
  rw [DC.emb_mulVec_of _ hv, Matrix.smul_mulVec, Matrix.one_mulVec, DC.jV_smul, jV_wbPart hv]

theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  unfold fvec
  rw [dif_neg (by simp)]

end cWLemmas

theorem lower_unipotent_rotation_holds : LowerUnipotentRotation := by
  intro k r z z' hz E _ _ θ Y f g _
  have hy : ∀ j, Q.yv k r z (Fin.last r) (cW k r θ * g) j =
      Complex.exp (-((θ : ℂ) * Complex.I)) * Q.yv k r z (Fin.last r) g j := by
    intro j
    unfold Q.yv
    rw [fvec_last, Matrix.mul_inv_rev, cW_inv, ← Matrix.mulVec_mulVec, cW_mulVec _ hz, Matrix.mulVec_smul, Pi.smul_apply,
      smul_eq_mul]
    congr 2
    push_cast
    ring
  have hq : ∀ (t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ),
      qminorOp (Q.EH k r) a b u (fun x => f (cW k r θ * x)) g = qminorOp (Q.EH k r) a b u f (cW k r θ * g) :=
    fun t a b u => congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian E _ t (Hpk k r) f a b u (cW k r θ)) g
  change (-(Q.chatL (Q.EH k r) (Q.posL k r (Fin.last r)) (Q.uC k r (Fin.last r) Y) (Q.yv k r z (Fin.last r))
      (fun _ => Q.xbv k r z' (Fin.last r)) f)) (cW k r θ * g) =
    Complex.exp (-((θ : ℂ) * Complex.I)) • (-(Q.chatL (Q.EH k r) (Q.posL k r (Fin.last r)) (Q.uC k r (Fin.last r) Y)
      (Q.yv k r z (Fin.last r)) (fun _ => Q.xbv k r z' (Fin.last r)) (fun x => f (cW k r θ * x)))) g
  simp only [Pi.neg_apply, Q.chatL, smul_neg, Finset.smul_sum, neg_inj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hy, hq, smul_smul]
  congr 1
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
