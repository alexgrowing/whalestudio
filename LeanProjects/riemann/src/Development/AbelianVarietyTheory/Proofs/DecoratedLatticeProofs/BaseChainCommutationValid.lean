import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTypePlacesOfLevCh
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseChain

def levAt {D : D7} {T : Type} (L : LevCh D T) (t : T) : LevCh D Unit :=
  { L with xiH := fun _ => L.xiH t, xi := fun _ => L.xi t, Q := fun _ => L.Q t, xiR := fun _ => L.xiR t }

theorem levAt_is {D : D7} {T : Type} {L : LevCh D T} {t : T} (h : L.Is t) : (levAt L t).Is () :=
  { mu0 := h.mu0, eta := h.eta, xi := fun _ => h.xi t, xi_inj := fun _ _ _ => rfl, xi_base := h.xi_base,
    xi_fin := fun _ => h.xi_fin t, xi_triv := fun _ => h.xi_triv t, xi_tame := fun _ => h.xi_tame t, Pg := h.Pg,
    Q_pl := fun _ => h.Q_pl t, Q_off := fun _ => h.Q_off t,
    Q_de := fun p hp => (h.Q_de p hp).imp fun _ H _ => H t,
    Q_ram := fun _ => h.Q_ram t, chi := h.chi, xiR := fun _ => h.xiR t, βY := h.βY, βX := h.βX, βV := h.βV, βW := h.βW }

theorem chrEq_mu_base {D : D7} {T : Type} {L : LevCh D T} {t : T} (h : L.Is t) (j : Fin D.R.m) :
    ChrEq (L.mu t ((j : ℕ) + 1)) (L.C.mu0 j) := by
  have h1 := GlobalTheory.Mem.TupChar.chrEq_mul (h.mu0 j) (h.xi t)
  rw [h.xi_base, mul_one] at h1
  exact h1

theorem com_is : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → (GlobalTheory.BaseChain.com W).Is := by
  intro D L hT Gi Gl Kc Yd cX ex W hP
  obtain ⟨-, -, -, hC, -⟩ := hP.bot.hyp
  have h2 := D.R.two_le_m
  exact GlobalTheory.SeeSaw.ComCols.com_is_of_levCh (levAt_is hC.lev) (com W) hC.models.inf
    (hC.chain.ωY W.P.A3.A.μ0 0 (by omega)).std rfl (chrEq_mu_base hC.lev) hC.lev.eta hC.lev.chi

end GlobalTheory.BaseChain
