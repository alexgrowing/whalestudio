import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteAllLifts
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SupLaw

theorem hkComm_of_ties : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), HkComm D := by
  intro D X E Y
  have hC : GlobalTheory.ExportPin.Model.Covered X.R := GlobalTheory.ExportPin.Model.covered_of_allPlaces X.R X.char.lev X.char.allPl
  exact hkComm_of_family X.R X.cG Y.S Y.YS Y.H.hL Y.H.hs Y.H.cHk Y.H.hkEq fun i j a b k P k' P' hk hk' =>
    family_comm X.R X.cG Y.S Y.YS X.char.lev X.char.fam X.char.models.HW
      (fun n => GlobalTheory.ExportPin.Model.j_injective X.R X.unif n _) hC Y.H.hL
      (fun i n k P hk α R ha hR => ⟨_, fun x => Y.reads n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) hk.2.1 α R ha hR x⟩)
      i j a b k P k' P' hk hk'

end GlobalTheory.SupLaw

end
