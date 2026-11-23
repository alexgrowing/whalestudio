import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesPt

noncomputable section

namespace Formalism.MainNotions.S.ThB

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.S.Pv.Frames

variable (D : D7)

def JSqRot {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (γ : Point D.host.E (D.R.rS + 1)) : ENNReal :=
  ∏ v, orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ))

def BSumRot {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (W : Point D.host.E (D.R.rS + 1) → ℝ) : ENNReal :=
  ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ},
    ENNReal.ofReal (wPt D γ.1 * ptWeightG D (rhoReal D) T T' γ.1.1 * W γ.1) * JSqRot D X γ.1

def RotatedFirstBound (Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    BSumRot D X (fun _ => 1) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

def RotatedWeightedBound (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    (∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    BSumRot D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

end Formalism.MainNotions.S.ThB
