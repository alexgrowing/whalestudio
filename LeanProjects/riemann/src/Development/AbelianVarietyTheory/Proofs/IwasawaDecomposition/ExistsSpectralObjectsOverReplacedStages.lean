import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RelabelledWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralLevelObjectsReplacedStagesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultREqReL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvEvHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MvRowJ

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.SRe

section Parts

variable {B : Base} {C : Cols B} (a : Late B C) (Z : New a.D) {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
  {A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]
  {F0 : ∀ u, Forms0 a.D u} (P : SPack a.D F0) {F₁ : ∀ u, Forms0 (reL a Z).D u} (hs : SameL a Z F0 F₁)
  (hF : FinX (reY Z P.Y))

set_option maxHeartbeats 4000000 in

def packL : SPack (reL a Z).D F₁ := (by with_unfolding_all exact ((P.re Z hs hF) :))

set_option maxHeartbeats 4000000 in

def restL (S : SRest (P.re Z hs hF)) : SRest (packL a Z P hs hF) := (by with_unfolding_all exact (S :))

set_option maxHeartbeats 4000000 in

theorem restL_j (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) :
    (restL a Z P hs hF S).j = (by with_unfolding_all exact (j.trans (eEECre Z P.G) :)) := (by with_unfolding_all exact (hS :))

set_option maxHeartbeats 4000000 in

theorem nonempty_sAtL (R : RealDat a.D A Ks) (F : Face a.D A) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H)
    (t : GA a.D (a.D.sp.Y 0)) (c : ℝ) (hc : 0 < c) (see : SeeAt R F P.X P.inst t)
    (ev : EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c)
    (j : a.D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) (rowJ : RowJ R eE P.X P.inst P.G t j)
    (S : SRest (P.re Z hs hF)) (hS : S.j = j.trans (eEECre Z P.G)) : Nonempty (SAtL a Z R F eE F₁) := by
  have h1 := mvRowJ a Z R P.X P.inst P.G t eE j rowJ
  have h2 := restL_j a Z P hs hF j S hS
  letI := alg (reL a Z) iK
  exact ⟨{ P := packL a Z P hs hF
           S := restL a Z P hs hF S
           t := tL a Z t
           c := c
           c_pos := hc
           see := (by with_unfolding_all exact ((mvSee a Z R F P.X P.inst t see) :))
           ev := (by with_unfolding_all exact ((mvEv_holds a Z R F P.X P.inst P.G t c ev) :))
           rowJ := by rw [h2]; exact (by with_unfolding_all exact (h1 :)) }⟩

end Parts

set_option maxHeartbeats 4000000 in

theorem satOfDiscreteSeries : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (P : SPack a.D F0), GapHyp a.D → Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D → a.D.what₂.Dstar = StandardLattice.DstarD a.D → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed a.D → R.IsModels → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → DallTie R F → ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ R F eE F₁) := by
  intro h1 h2 h3 h4 h5 B C a G' _ _ Pl0 T A Ks _ _ _ R F F0 eE P hG hI hL hRT hDs hLev hgl hPin hE0 hMod hRg hN hDall
  obtain ⟨hD, j, t, c, hc, see, ev, rowJ, rest⟩ := GlobalTheory.T.exists_spectralLevel_objects_replacedStages h1 h2 h3 h4 h5 a.D G' Pl0 T A Ks R F F0 P eE hG hI hL hRT hDs
    hLev hgl hPin hE0 hMod hRg hN hDall
  refine ⟨P.toNew hD j, fun N hh F₁ hs => ?_⟩
  obtain ⟨hF, S, hS⟩ := rest N hh _ hs
  exact nonempty_sAtL a _ P hs hF R F eE t c hc see ev j rowJ S hS

end GlobalTheory.Mem.SRe

end
