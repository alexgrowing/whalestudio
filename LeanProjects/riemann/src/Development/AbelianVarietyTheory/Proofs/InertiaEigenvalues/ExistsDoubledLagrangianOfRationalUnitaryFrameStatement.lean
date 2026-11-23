import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDoubledLagrangianOfRationalUnitaryFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubledLagrangian_of_rational_unitary_frame : ∀ (D : D7) (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∃ Y : Lag W, IsLagFrame W Y (frameOf W g₀) := by
  first | exact @GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf | exact GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf | (intros; apply GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf <;> assumption)
