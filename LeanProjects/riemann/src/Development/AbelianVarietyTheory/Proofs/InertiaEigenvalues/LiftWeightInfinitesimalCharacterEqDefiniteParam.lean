import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfLamLdefEqParamV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.InertiaEigenvalues.LamParam

theorem infOf_lamV_eq_paramV : ∀ (D : D7) (j : Fin D.R.m) (hn : (Vc D j).rank = D.R.nV) (t : D.what₂.Tau), NG.infOf (fun a : Fin D.R.nV => (FWT.lamV D j t).w (Fin.cast hn.symm a)) = NG.paramV D.R (D.hc t) j (1 / 2) := by
  intro D j hn t
  have h := GlobalTheory.Mem.WtPar.infOf_lamLdef_eq_paramV D j t
  rw [← h]
  show NG.infOf (fun a : Fin D.R.nV => (Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) t).w (Fin.cast hn.symm a)) = _
  revert hn
  generalize (Vc D j).rank = n
  intro hn
  subst hn
  rfl

end GlobalTheory.InertiaEigenvalues.LamParam
