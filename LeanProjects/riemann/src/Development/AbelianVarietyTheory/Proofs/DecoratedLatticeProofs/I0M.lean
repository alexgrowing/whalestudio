import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.SBesEx

variable {D : D7}

def cY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    Fin (D.sp.Y 0).rank → D.host.E :=
  fun k => X.ιE (X.crd y (Fin.cast (rank_eq X h) k))

def scl (t lam : D.host.E) (a : Fin D.R.rS) : D.host.E := t * lam ^ (D.R.rS - (a : ℕ))

def eM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin D.R.rS) D.host.E :=
  fun k a => scl t lam a * cY X h (X.eX a) k

def e'M (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin D.R.rS) D.host.E :=
  fun k a => (star (scl t lam a))⁻¹ * cY X h (X.fY a) k

def qM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.X 0).rank) D.host.E :=
  fun k j => X.ιE (X.crd (Formalism.L2.SG.ColDict.qFr wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j))
    (Fin.cast (rank_eq X h) k))

def zM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t : D.host.E) (L : HSp D) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin L.rank) D.host.E :=
  fun k _ => t * cY X h (X.zu u) k

def i0M (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (t : D.host.E) {V₀ L : HSp D} (o : OrthDec V₀ (D.sp.X 0) L) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin V₀.rank) D.host.E :=
  qM X h wt * o.qA + zM X h u t L * o.qB

def zeta (L : HSp D) : Fin L.rank → D.host.E := fun _ => 1

end GlobalTheory.Core.SBesEx

end
