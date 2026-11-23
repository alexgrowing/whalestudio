import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLv3MvFixH
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpectralObjectsOverReplacedStagesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColsTiedSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RangeEEAndNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapHypOfNodes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSPackIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiscreteSeriesFormalDegreeProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHyperplaneVolumeRatioSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarCoeffOfEqReverse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfMemSuppSpan

noncomputable section

namespace GlobalTheory.Mem.SRe.UpS

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowHyp {D : D7} (p : RowPk D) : Prop :=
  p.R.toLevCh.Is p.A.μ0 ∧ p.R.grp_levels p.F ∧ GrpPin p.R ∧ p.R.IsModels ∧
    LinearMap.range p.eE = (p.R.EEat (p.R.levR p.F true)).comap p.R.HE.e ∧
    (∀ x, ‖p.eE x‖ ^ 2 = RealDat.nP p.F true * ‖x‖ ^ 2) ∧ DallTie p.R p.F

set_option maxHeartbeats 4000000 in

theorem rowHyp_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : R3.Pins R F cG)
    (hH : R3.Holds R F) : RowHyp (⟨G, Pl0, T, A3.A, Ks, R.toRealDat, F.lv2, Y.eE⟩ : RowPk D) := by
  have hr := R3.RowsLvl.range_eE_and_norm D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨plg, iso, h⟩ := hP.keep.grp
  exact ⟨hP.char.base.lev, hP.char.base.grp.levels, ⟨R.eG.trans cG, plg, iso, h⟩, hP.char.base.models, hr.1, hr.2, Y.dall⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 4000000 in

theorem rowHyp_pkOf {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) : RowHyp (pkOf r) :=
  (by with_unfolding_all exact ((rowHyp_read r.r.z.R r.r.z.F r.r.z.cG r.r.Y r.r.z.pins r.r.intersectionNumber_baseChange) :))

def reSt {C : Cols B} (a : Late B C) (Zs : SNew a.D) : SStage B C a.W := reStage a.st Zs

def SatNew : Prop :=
  ∀ (B : Base) (C : Cols B) (a : Late B C) (p : RowPk a.D) (F0 : ∀ u, Forms0 a.D u) (P : SPack a.D F0), GapHyp a.D →
    Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D →
    a.D.what₂.Dstar = StandardLattice.DstarD a.D → IdempotentRealFixed a.D → RowHyp p →
    ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁)

set_option maxHeartbeats 4000000 in
theorem satOfDiscreteSeries (h1 : GlobalTheory.Dec.DSInfChar) (h2 : GlobalTheory.Published.HarishChandraFinite) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.DiscreteSeriesUpqUnique) (h5 : Formalism.L2.SG.RowsDef.RowsFinDim) : SatNew :=
  fun B C a p F0 P g i l r d e ⟨a1, a2, a3, a4, a5, a6, a7⟩ =>
    GlobalTheory.T.exists_spectralObjects_over_replacedStages h1 h2 h3 h4 h5 B C a p.G' p.Pl0 p.T p.A p.Ks p.R p.F F0 p.eE P g i l r d a1 a2 a3 e a4 a5 a6 a7

set_option maxHeartbeats 8000000 in

theorem sat_col (a : w.Lt) (col : ColT w a) (p : RowPk (Late.D a)) (Zs : SNew (Late.D a))
    (H : ∀ (N : ∀ u, Submodule (𝓞 (Late.D a).what₂.LL) ((Late.D a).div.Nu u).V) (hh : (Late.D a).what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ (fun u => (col.C.forms u).to0) F₁ →
        Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁))
    (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) (col' : ColT w (upL a (reSt a Zs) N h)) :
    Nonempty ((p.up a (reSt a Zs) N h).SAt fun u => (col'.C.forms u).to0) := by
  let Zn : New (Late.D a) := ⟨Zs, (by with_unfolding_all exact (N :)), (by with_unfolding_all exact (h :))⟩
  obtain ⟨C', hC⟩ := ColRe.exists_colsTiedSym (Late.D a) Zn col.C
  let F₀ : ∀ u, Forms0 (reD (Late.D a) Zn) u := fun u => (C'.forms u).to0
  let F₁ : ∀ u, Forms0 (reL a Zn).D u := (by with_unfolding_all exact (F₀ :))
  have hF : SameL a Zn (fun u => (col.C.forms u).to0) F₁ := (by with_unfolding_all exact (hC :))
  obtain ⟨s⟩ := H Zn.N Zn.h F₁ hF
  have c := CarModel.sameStd B f T w a Zn col ((by with_unfolding_all exact (col' :))) F₁ hF
  exact ⟨CarModel.satCar (D := Late.D (upL a (reSt a Zs) N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) (p.up a (reSt a Zs) N h) ((by with_unfolding_all exact (s :)))⟩

def RealOf : Prop := ∀ D : D7, VolTieG D → D.s.cdScale = Vol.trueScale D.cd → (∀ τ, D.dsig τ = Vol.trueDsig D.R (D.hc τ)) → RealTied D

def PackEx : Prop := ∀ (D : D7) (F : ∀ u, Forms0 D u), GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D →
  ∃ P : SPack D F, Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I)

set_option maxHeartbeats 4000000 in

theorem real_of (hR : RealOf) (a : w.Lt) (g : GIs2 K w a.G) (hs : a.S.s.cdScale = Vol.trueScale a.G.cd)
    (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ)) : RealTied (w.D a) :=
  hR (w.D a) (g a.W a.V a.S a.N).1 ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :)))

set_option maxHeartbeats 8000000 in

theorem lv4_of {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) (hO : K.Over B.toPre)
    (a : w.Lt) (l : Lv3 p.s K w a) (gap : GapHyp (Late.D a)) (hdel : a.S.s.Del = (Delv K.s K.cD : ℚ))
    (hs : a.S.s.cdScale = Vol.trueScale a.G.cd) (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ))
    (loc : Formalism.L2.SG.Pf.LocCP.LocTied (Late.D a)) : ∃ b : w.Lt, Nonempty (Lv4 p.s K w b) := by
  obtain ⟨vt, -, ⟨col⟩⟩ := l.g a.W a.V a.S a.N
  have col₀ : ColT w a := col.toColT
  obtain ⟨P, hI⟩ := hP (Late.D a) (fun u => (col₀.C.forms u).to0) gap loc
  have real₀ : RealTied (Late.D a) := (by with_unfolding_all exact ((real_of hR a l.g hs hd) :))
  have dstar : (Late.D a).what₂.Dstar = StandardLattice.DstarD (Late.D a) := (sizes_eq_count K (Late.st a) hO (hV _ real₀.vol) hd).2
  have e0 : IdempotentRealFixed (Late.D a) := hE _ (l.what₂.grp.eSerTie a.V a.S a.G)
  obtain ⟨Zs, H⟩ := hN B w.C a (pkOf l.what₂) _ P gap hI loc real₀ dstar e0 (rowHyp_pkOf l.what₂)
  let b : w.Lt := upL a (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨l', e⟩ := hM K B f T w a l (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨-, -, ⟨col'⟩⟩ := l'.g b.W b.V b.S b.N
  have col₁ : ColumnDataSplitPrimes K w b := col'
  obtain ⟨s⟩ := sat_col a col₀ (pkOf l.what₂) Zs H _ _ col₁.toColT
  have s' : SX K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT := by
    rw [sx_eq l'.what₂ col₁.toColT, e]
    exact s
  have x : p.S K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT s' := by
    rw [hS]
    exact PUnit.unit
  exact ⟨b, ⟨⟨l', col₁, real_of hR b l'.g ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :))), (by with_unfolding_all exact (hd :)), (by with_unfolding_all exact (hdel :)), ⟨s', x⟩⟩⟩⟩

set_option maxHeartbeats 8000000 in

theorem step_of {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) :
    StepW (pinAnd (Has3 p.s)) (Has4 p.s) := by
  refine Step.of_evG ((evG_of_ev GlobalTheory.Mem.Top.NodeGap.ev_gapHyp).imp fun K _ _ _ _ gap B f T hO _ _ _ w => ?_)
  rintro ⟨-, Z, ⟨l⟩⟩
  obtain ⟨S, hdel, hs, hd, loc⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C Z.W Z.G.cd hO (SpectralModel.colsPos_of Z.S) (SpectralModel.rows_le_of Z.S)
  obtain ⟨l₀, -⟩ := hM K B f T w Z l S (fun u => (Z.V.div.Nu u).L) Z.V.div.h
  exact lv4_of p hS hM hN hR hP hV hE hO _ l₀ (gap _ hO) hdel hs hd ((by with_unfolding_all exact ((loc (upL Z S (fun u => (Z.V.div.Nu u).L) Z.V.div.h).V Z.N Z.G) :)))

theorem realOf (h1 : Vol.DiscreteSeriesExist) (h2 : Vol.FormalDegreeFormula₂) : RealOf := by
  intro D hv hs hd
  refine ⟨?_, ?_, ?_, hv⟩
  · rw [Vol.cdScaleTie_iff, hs]
    exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd
  · intro τ
    unfold Formalism.L2.Theta.IsDsig
    rw [hs, hd τ]
    exact (GlobalTheory.T.exists_discreteSeries_formalDegree_product h1 h2 D.cd D.R (D.hc τ)).1
  · intro τ H _ _ σ d hσ hf
    rw [hs] at hf
    rw [hd τ]
    exact (GlobalTheory.T.exists_discreteSeries_formalDegree_product h1 h2 D.cd D.R (D.hc τ)).2 H σ d hσ hf

theorem goodIdempotent_real_of_harishChandra_series (D : D7) (h : GlobalTheory.GLq.ESerTie D) : IdempotentRealFixed D :=
  GlobalTheory.GoodIdemReal.star_coeff_of_reverse D fun k g hm h0 x => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨L, -, he⟩ := h k
    rw [he, he]
    exact DFunLike.congr_fun (GlobalTheory.GLq.GalSer.eSerC_map L _ D.R.r hm (GlobalTheory.SeriesSupport.rel_dual L hm h0)) x

theorem stepW_has4 : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), p.S = SExt.none → LevelThreeCondition p.s → StepW (pinAnd (Has3 p.s)) (Has4 p.s) :=
  fun h1 h2 h3 h4 h5 hW hB hD hF _ _ p hS hM =>
    step_of p hS hM (satOfDiscreteSeries h1 h2 h3 h4 h5) (realOf hD hF) (GlobalTheory.Mem.SRe.exists_sPack_integrable hW hB h5)
      (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hW)) goodIdempotent_real_of_harishChandra_series

end GlobalTheory.Mem.SRe.UpS

end
