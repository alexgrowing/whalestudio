import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

variable {D : D7} {u : D.what₂.Word}

def LevX (F : Formalism.L2.Forms.Forms0 D u) (d : GlobalTheory.SeeSaw.Dat D u) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) : Prop :=
  ∀ a ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) a = y.1.1 →
    ((y : GL _ _) ∈ F.cls0.lev.U ↔
      (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o a * d.t 0 ∈ d.lev 0) ∧
    ∀ hy : (y : GL _ _) ∈ F.cls0.lev.U, ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) *
      levChi (d.st 0).V (d.st 0).β (d.st 0).L
        ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o a * d.t 0) = 1

def BesselCompatibility {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) :
    Prop :=
  ∃ B : SBes S.X S.inst u d.c.ψ (D.sp.X 0), B.lev = d.B 0 D.R.rS h0 ∧ B.Adapted (S.tr u).wt

end GlobalTheory.Core.Mi

end
