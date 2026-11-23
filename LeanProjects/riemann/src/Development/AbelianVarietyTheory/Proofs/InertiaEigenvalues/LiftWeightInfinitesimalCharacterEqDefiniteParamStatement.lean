import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftWeightInfinitesimalCharacterEqDefiniteParam
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_weight_infinitesimal_character_eq_definite_param : ∀ (D : D7) (j : Fin D.R.m) (hn : (Vc D j).rank = D.R.nV) (t : D.what₂.Tau), NG.infOf (fun a : Fin D.R.nV => (FWT.lamV D j t).w (Fin.cast hn.symm a)) = NG.paramV D.R (D.hc t) j (1 / 2) := by
  first | exact @GlobalTheory.InertiaEigenvalues.LamParam.infOf_lamV_eq_paramV | exact GlobalTheory.InertiaEigenvalues.LamParam.infOf_lamV_eq_paramV | (intros; apply GlobalTheory.InertiaEigenvalues.LamParam.infOf_lamV_eq_paramV <;> assumption)
