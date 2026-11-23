import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.DiscreteGroups.GlobalIrreducibility.IneEqOfHasGreenLe
import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe

noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf GlobalTheory.SerSys GlobalTheory.SerSys.Bridge
open scoped Classical

attribute [local instance] GlobalTheory.SerSys.Bridge.factT

theorem labParamLe_of (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) :
    LabParamLe D.R.nV D L rc := fun k v n hn π hπ f hf =>
  ine_eq_of_has_green_le D.R.nV (OfLabel.ofLabel (L k) (five_le D k) hG) (L k) _ _ _ (h1 k v) (h2 k) hG (h3 k v)
    (labelsCusp _ _ _) ⟨n, π⟩ hn hπ.1 hπ.2 f hf

theorem serLocLe_of (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : LocComp D rc) (hP : LabParamLe D.R.nV D L rc) : SerLoc D :=
  have hS : ∀ k, (OfLabel.ofLabel (L k) (five_le D k) hG).IsOf (L k) := fun _ _ _ => rfl
  GlobalTheory.SerLocal.serLoc D _ (hL.sysTie hS) hU (locType_of_tiesLe hL hS hC hP)

theorem serLoc_of_tiesLe (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : LocComp D rc)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) : SerLoc D :=
  serLocLe_of D L rc hG hL hU hC (labParamLe_of D L rc hG h1 h2 h3)

end DiscreteGroups.sglob.DzType.Rt

end
