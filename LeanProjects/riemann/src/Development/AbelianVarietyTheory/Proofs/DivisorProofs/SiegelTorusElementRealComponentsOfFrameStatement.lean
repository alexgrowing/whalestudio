import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementRealComponentsOfFrame
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTorusElement_real_components_of_frame : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Fin r → ℝ) (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a).map (finPart D) = 1 ∧ ∀ τ, Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * X.map (tauE D τ) = X.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) ∧ Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Y.map (tauE D τ) = Y.map (tauE D τ) * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) ∧ ∀ z : Fin V.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) *ᵥ z = 0 → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) *ᵥ z = 0 → Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *ᵥ (fun i => tauE D τ (z i)) = fun i => tauE D τ (z i) := by
  first | exact @GlobalTheory.TorusDict.torus_dict | exact GlobalTheory.TorusDict.torus_dict | (intros; apply GlobalTheory.TorusDict.torus_dict <;> assumption)
