import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowBlockExponentConditionOfJumpWindow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JumpWindow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumpWindowBlockExponentCondition_of_jumpWindow : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h₁ : ℕ), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → D.R.t ≤ h₁ → GlobalTheory.BlockWindow.JumpWindow D i r π h₁ → GlobalTheory.BlockWindow.JointTB D HW F i r π h₁ h₁ (GlobalTheory.HubLoc.cBnum (D.nd.l i) h₁ D.R.t (4 * D.R.n * D.R.nV)) := by
  first | exact @GlobalTheory.BlockWindow.jointTB_of_jumpWindow | exact GlobalTheory.BlockWindow.jointTB_of_jumpWindow | (intros; apply GlobalTheory.BlockWindow.jointTB_of_jumpWindow <;> assumption)
