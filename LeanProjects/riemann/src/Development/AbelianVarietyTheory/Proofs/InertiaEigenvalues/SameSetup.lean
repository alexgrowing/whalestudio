import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.Move

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def CopyTw.cm (h : CopyTw D D' ι e) (j : Fin D.R.m) : Fin D'.R.m :=
  Fin.cast (congrArg Ranks.m h.gal.R) j

theorem CopyTw.cm_val (h : CopyTw D D' ι e) (j : Fin D.R.m) : ((h.cm j : Fin D'.R.m) : ℕ) = j := rfl

abbrev SameSetup (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) : Prop := SameData ρ ρ'

theorem SameSetup.refl (ρ : Setup D.ntw) : SameSetup ρ ρ := SameData.refl ρ

def RdRel (h : CopyTw D D' ι e) {ρ : Setup D.ntw} {ρ' : Setup D'.ntw} (rd : Rds D.nexp ρ) (rd' : Rds D'.nexp ρ') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw) (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (f : D.nexp.Fm i ((j : ℕ) + 1) b),
    HEq (rd' i' (h.cm j) b (h.fmCast hi ((j : ℕ) + 1) b f)) (rd i j b f)

theorem RdRel.refl (D : D7) {ρ : Setup D.ntw} (rd : Rds D.nexp ρ) : RdRel (CopyTw.refl D) rd rd := fun i i' hi j b f => by
  cases hi; exact HEq.rfl

end GlobalTheory.TwInputs.Move

end
