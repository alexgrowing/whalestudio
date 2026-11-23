import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MemBlockTriangularTwoBlockSizesOfLe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChain

theorem levFn_datY_noQ {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm) (x : GL (Fin V.rank) (Lev.EAf D)) :
    levFn β (Lev.datY V.rank r t j hr Pg Q P χ ξ fr) x = levFn β (Lev.datY V.rank r t j hr Pg ∅ P χ ξ' fr) x := by
  unfold levFn
  have hq : ∀ PP ∈ (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).Q,
      (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).xq PP
        (dBlk (blk2 (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r) 1 (redFn β PP x)) = 1 := by
    intro PP _
    show _ = 1
    rw [show (Lev.datY V.rank r t j hr Pg Q P χ ξ fr).r = r from rfl, Formalism.IndefR.Eqv.Act.block_determinant_empty_eq_one hn, map_one]
  rw [Finset.prod_eq_one hq]
  rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem levS_datYt_base (W : RealPack ex) :
    levS (Yc D 0) ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)) = levS (Yc D 0) ((pk W).βY 0) ((pk W).dat0 (lvP W)) := by
  have e : Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)) =
      Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram ((pk W).βY 0) ((pk W).dat0 (lvP W)) := by
    refine Subgroup.ext fun x => ?_
    show (x ∈ parLev _ _ _ _ ∧ _) ↔ (x ∈ parLev _ _ _ _ ∧ _)
    unfold LevCh.datYt LevCh.dat0
    rw [Formalism.IndefR.Eqv.Act.mem_parLev_datY_noQ Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (pk W).Pg
      ((pk W).Q W.P.A3.A.μ0) (lvP W) (pk W).chi ((pk W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B x]
    rfl
  unfold levS Lev.levG
  rw [e]

theorem levChi_datYt_base (W : RealPack ex) :
    Lev.levChi (Yc D 0) ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)) =
      Lev.levChi (Yc D 0) ((pk W).βY 0) ((pk W).dat0 (lvP W)) := by
  funext k
  unfold Lev.levChi LevCh.datYt LevCh.dat0
  rw [levFn_datY_noQ ((pk W).βY 0) Formalism.IndefR.Eqv.Act.rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 (pk W).Pg
      ((pk W).Q W.P.A3.A.μ0) (lvP W) (pk W).chi ((pk W).xiR W.P.A3.A.μ0) (fun _ => 1) Lev.Frm.B]

theorem rows_mem_CC : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ T ∈ ThetaLiftSpaceZero W, T ∈ (GlobalTheory.BaseChain.stageY W 0).CC (GlobalTheory.BaseChain.com W) := by
  intro D L hT Gi Gl Kc Yd cX ex W _ T hT0
  show T ∈ MultT (pk W).θ ((pk W).MY 0) (levS (Yc D 0) ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)))
    (Lev.levChi (Yc D 0) ((pk W).βY 0) ((pk W).datYt W.P.A3.A.μ0 0 (lvP W)))
  rw [levS_datYt_base W, levChi_datYt_base W]
  exact hT0

end GlobalTheory.BaseChain

end
