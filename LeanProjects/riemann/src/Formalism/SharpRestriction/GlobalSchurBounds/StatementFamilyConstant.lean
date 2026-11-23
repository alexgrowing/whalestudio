import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

noncomputable section

namespace Formalism.MainNotions.TwistedThetaFamilies

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def TwistedThetaFamily (D : D7) (C : ℝ) : Prop := GL3Theta.TwistedThetaTheorem D C fun cc δ e => StandardLatticesGL3.natTie D cc δ e

theorem TwistedThetaFamily.toE {D : D7} {C : ℝ} (h : TwistedThetaFamily D C) : GL3Theta.ConclusionE D C :=
  GL3Theta.TwistedThetaTheorem.mono (fun _ _ _ _ => trivial) h

def Stmt (D : D7) (C : ℝ) : Prop := GL3Theta.Adm3s D → StandardLatticesGL3.AdmDext D → GL3Theta.aux₃ D ∧ TwistedThetaFamily D C

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.AdmF Fm ∧ StandardLatticesGL3.AdmExtF Fm
def TwistedThetaOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop := GL3Theta.Fam (fun D => TwistedThetaFamily D C) Fm

def StatementFamilyConstant {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop := AdmF Fm → GL3Theta.ConclusionOnFamily Fm ∧ TwistedThetaOnFamily Fm C

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → GL3Theta.ConclusionOnFamily Fm ∧ ∃ C : ℝ, TwistedThetaOnFamily Fm C

end Formalism.MainNotions.TwistedThetaFamilies
