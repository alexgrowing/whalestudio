import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QEqColPer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainDownEqLiftAlongPath
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneLessEqTopBesselLevelPeriod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorsRowAndColumnPaths
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorOfRepresentingOppositePath
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorRightwardArrow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ErrorExponentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColconSplitFamAppend
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftTOppTens
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevJGridSuccIndep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow

variable {D : D7}

section Lin

variable {ψ : AddChar (AF D.host.F) ℂ} {T₀ : HSp D}

end Lin

theorem unitN_unique {S : HSp D} {ρ : ℕ} {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (he : IsIsoSub S e)
    {ν ν' : Measure (NFlag S e)} {𝓝 𝓝' : Set (NFlag S e)} (h : GlobalTheory.Per.IsUnitN S e ν 𝓝) (h' : GlobalTheory.Per.IsUnitN S e ν' 𝓝') :
    ν = ν' := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S he
  haveI : Countable (NFlagQ S e) := by
    have hinj : Function.Injective (fun x : NFlagQ S e => (⟨x.1.1, x.2⟩ : GQ S)) := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : GQ S => z.1) hxy))
    exact hinj.countable
  haveI := h.1
  haveI := h'.1
  have hs := Measure.isMulLeftInvariant_eq_smul ν ν'
  have hac : ν ≪ ν' := by rw [hs]; exact Measure.smul_absolutelyContinuous
  have h2 : ν 𝓝' = 1 := ((h'.2.1.mono hac).measure_eq h.2.1).trans h.2.2
  have h3 : ν 𝓝' = Measure.haarScalarFactor ν ν' := by
    conv_lhs => rw [hs]
    simp [h'.2.2]
  rw [hs, ENNReal.coe_eq_one.1 (h3.symm.trans h2), one_smul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem per_indep {ρ : ℕ} (B : GlobalTheory.Unf.BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {μ : Measure (GA D B.A)} (hA : μ = B.vA.μ) {𝓕 : Set (GA D B.A)} (h2 : IsFundamentalDomain (GQ B.A) 𝓕 μ)
    {ν : Measure (flagN B.d)} {𝓝 : Set (flagN B.d)} (hu : GlobalTheory.Per.IsUnitN B.V B.d.e ν 𝓝) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ)
    (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g) (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) :
    besPer ψ 1 B.d B.o B.ζ μ 𝓕 ν 𝓝 φ f = B.per ψ φ f := by
  have hI : IsIsoSub B.V B.d.e := ⟨GlobalTheory.Core.Mi.PerCmp.hyp_linIndep B.d, by rw [cT_sig]; exact B.d.ee⟩
  obtain rfl : ν = B.vN.ν := unitN_unique hI hu B.vN.unit
  subst hA
  rw [GlobalTheory.Core.Mi.PerCmp.besPer_domN B.d B.o B.ζ hψ 1 _ _ B.vN.ν B.vN.unit.1 hu.2.1 B.vN.unit.2.1 φ f hf]
  exact GlobalTheory.Core.Mi.PerCmp.besPer_domA B hψ h2 φ f hφ hf

theorem hN_top {M : Vol G} {t : T} (hM : M.Is t) : NFlag (G.V (.grid D.R.m 0)) G.besTop.e = flagN (topLev G hM).d :=
  (nFlag_diag (GlobalTheory.RowUnf.rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2)
    (by have := top_idx (D := D); omega)).e (lam _) (lam_ne _)).symm

def topVNRow {M₀ : Vol G} (h₀ : M₀.IsRow) : GlobalTheory.Unf.VolN (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) :=
  volNOf (d := GlobalTheory.RowUnf.rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2) (by have := top_idx (D := D); omega))
    (nFlag_diag _ (lam _) (lam_ne _)).symm
    (GlobalTheory.RowUnf.topVolN G M₀ h₀ (by have := D.R.two_le_m; omega) (by have := top_idx (D := D); omega))

theorem bplus_eq_besPer (W : G.Weil) {M₀ : Vol G} (h₀ : M₀.IsRow) {M : Vol G} {t : T} (hM : M.Is t) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) : Bplus W M₀ φ F = besPer W.ψ 1 (topLev G hM).d (topLev G hM).o (topLev G hM).ζ (M₀.ν (.top 0))
      (M₀.fd (.top 0)) (topVNRow h₀).ν (topVNRow h₀).𝓝 φ F := by
  have hN := hN_top hM
  show _ = ∫ h in M₀.fd (.top 0), ∫ n in trSet hN M₀.fdN,
      GlobalTheory.MixPer.besFun W.ψ 1 (topLev G hM).d (topLev G hM).o (topLev G hM).ζ φ F h n ∂(trMeas hN M₀.νN) ∂M₀.ν (.top 0)
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  refine (TopPer.integral_tr hN M₀.νN M₀.fdN fun g => φ h * F (g * embTop G h) * star (besChar W.ψ G.besTop g)).symm.trans ?_
  refine integral_congr_ae (ae_of_all _ fun n => ?_)
  show φ h * F (n.1 * embTop G h) * star (besChar W.ψ G.besTop n.1) =
    φ h * F ((show GA D (topLev G hM).V from n.1) * GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h) *
      star (psiBes W.ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n.1)
  rw [TopPer.embA_topLev G hM h, TopPer.psiBes_topLev G hM W.ψ n.1 n.2]
  rfl

theorem meas_top {M₀ M : Vol G} (h₀ : M₀.IsRow) {t : T} (hM : M.Is t) : M₀.ν (.top 0) = (topLev G hM).vA.μ :=
  GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M₀ M _ _ h₀.top hM.isRow.top

theorem bplus_indep (W : G.Weil) {M₀ M : Vol G} (h₀ : M₀.IsRow) {t : T} (hM : M.Is t) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) (hφ : ∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g)
    (hF : ∀ γ ∈ GQ (G.V (.grid D.R.m 0)), ∀ g, F (γ * g) = F g) : Bplus W M₀ φ F = Bplus W M φ F :=
  (bplus_eq_besPer W h₀ hM φ F).trans ((per_indep (topLev G hM) W.ψ_std.1 (meas_top h₀ hM) h₀.top.haar_fund.2
    (topVNRow h₀).unit φ F hφ hF).trans (TopPer.bplus_eq_topLev_per G W t _ hM φ F).symm)

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem bplus_add_right (W : G.Weil) (M : Vol G) {φ : Fn G (.top 0)} {F F' : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F)
    (h' : BplusConv W M φ F') : BplusConv W M φ (F + F') ∧ Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F' := by
  have e : ∀ x, besInt W φ (F + F') x = fun n => besInt W φ F x n + besInt W φ F' x n := fun x => funext fun n => by
    simp only [besInt, Pi.add_apply]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W φ (F + F') x n ∂M.νN =
      (∫ n in M.fdN, besInt W φ F x n ∂M.νN) + ∫ n in M.fdN, besInt W φ F' x n ∂M.νN := fun x => by
    rw [e x]; exact integral_add (h.1 x) (h'.1 x)
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).add (h'.1 x)
  · simp only [ei]; exact h.2.add h'.2
  · simp only [Bplus, ei]; exact integral_add h.2 h'.2

theorem bplus_smul_right (W : G.Weil) (M : Vol G) (c : ℂ) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)} (h : BplusConv W M φ F) :
    BplusConv W M φ (c • F) ∧ Bplus W M φ (c • F) = c * Bplus W M φ F := by
  have e : ∀ x, besInt W φ (c • F) x = fun n => c * besInt W φ F x n := fun x => funext fun n => by
    simp only [besInt, Pi.smul_apply, smul_eq_mul]; ring
  have ei : ∀ x, ∫ n in M.fdN, besInt W φ (c • F) x n ∂M.νN = c * ∫ n in M.fdN, besInt W φ F x n ∂M.νN := fun x => by
    rw [e x]; exact integral_const_mul _ _
  refine ⟨⟨fun x => ?_, ?_⟩, ?_⟩
  · rw [e x]; exact (h.1 x).const_mul c
  · simp only [ei]; exact h.2.const_mul c
  · simp only [Bplus, ei]; exact integral_const_mul _ _

theorem bplus_sum_right (W : G.Weil) (M : Vol G) (φ : Fn G (.top 0)) {ι : Type} (s : Finset ι) (F : ι → Fn G (.grid D.R.m 0))
    (h : ∀ i ∈ s, BplusConv W M φ (F i)) :
    BplusConv W M φ (∑ i ∈ s, F i) ∧ Bplus W M φ (∑ i ∈ s, F i) = ∑ i ∈ s, Bplus W M φ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : ∀ x, besInt W φ (0 : Fn G (.grid D.R.m 0)) x = fun _ => 0 := fun x => funext fun n => by simp [besInt]
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨⟨fun x => by rw [e x]; exact integrableOn_zero, ?_⟩, ?_⟩
    · simp only [e, integral_zero]; exact integrableOn_zero
    · simp only [Bplus, e, integral_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨h3, h4⟩ := bplus_add_right W M (h i (Finset.mem_insert_self _ _)) h1
    exact ⟨h3, by rw [h4, h2]⟩

theorem liftT_oppTens (W : G.Weil) (M : Vol G) (t : T) (τi : PolRow G × PolDown G →₀ ℂ) (τf : SchRow G × SchDown G t →₀ ℂ)
    (F : Fn G (.grid 0 D.R.m)) : liftT W M (oppPath t D.R.m) (oppTens W t τi τf) F =
      ∑ x ∈ τi.support ×ˢ τf.support, (τi x.1 * τf x.2) • liftP W M (oppPath t D.R.m) (oppPure W t x.1 x.2) F := by
  let l : TotT G (oppPath t D.R.m) →+ Fn G (.grid D.R.m 0) :=
    AddMonoidHom.mk' (fun τ => liftT W M (oppPath t D.R.m) τ F) fun τ τ' => liftT_add W M _ τ τ' F
  show l (oppTens W t τi τf) = _
  rw [oppTens, Finsupp.sum, map_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun d _ => liftT_single W M _ _ _ F

theorem all_append {S : Arrow T → Type} {P : ∀ a, S a → Prop} {X Y : Node} {p : Path T X Y} {d : p.Fam S} (hd : Path.Fam.All P d) :
    ∀ {Z : Node} (q : Path T Y Z) (e : q.Fam S), Path.Fam.All P e → Path.Fam.All P (Path.Fam.append (q := q) d e)
  | _, .nil, _, _ => hd
  | _, .snoc _ q, e, he => ⟨all_append hd q e.1 he.1, he.2⟩

theorem all_downFam {S : Arrow T → Type} {P : ∀ a, S a → Prop} (t : T) (i : ℕ) :
    ∀ n (f : ∀ j : Fin n, S (.down t i j)), (∀ j, P _ (f j)) → Path.Fam.All P (downFam t i n f)
  | 0, _, _ => trivial
  | n + 1, f, h => all_append (p := Path.one (.down t i n)) (d := ((), f (Fin.last n))) ⟨trivial, h (Fin.last n)⟩ _ _
      (all_downFam t i n _ fun j => h j.castSucc)

variable (W : G.Weil) (M : Vol G) (t : T)

def rowLift (P : PolRow G) (d : SchRow G) (F : Fn G (.grid 0 D.R.m)) : Fn G (.grid D.R.m D.R.m) :=
  liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (d i) (P i)) F

def downPure (P : PolDown G) (d : SchDown G t) : PureT G (downPath t D.R.m D.R.m) :=
  downFam t D.R.m D.R.m fun j => W.fock (.mu t D.R.m j) (d j) (P j)

variable {M t} in

def oppPer (hM : M.Is t) (P : PolRow G × PolDown G) (d : SchRow G × SchDown G t) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    (chain G W t hM).Var → ℂ :=
  colPer W hM _ 0 top_idx (topVN hM) (chainData G W t hM (downPure W t P.2 d.2)) (rowLift W M P.1 d.1 F) φ 1

theorem pathLift_oppositePure (P : PolRow G × PolDown G) (d : SchRow G × SchDown G t) (F : Fn G (.grid 0 D.R.m)) :
    liftP W M (oppPath t D.R.m) (oppPure W t P d) F =
      liftP W M (downPath t D.R.m D.R.m) (downPure W t P.2 d.2) (rowLift W M P.1 d.1 F) :=
  pathLift_comp W M _ _ F _ _

theorem allTheta_downPure (ρ : RealMatch W) (e : AE D) (φ d : SchDown G t)
    (h : ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ j) (d j)) (P : PolDown G) :
    AllTheta G W t (downPure W t P d) :=
  all_downFam t _ _ _ fun j => GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (h j).2 (ρ.vT_is t _ j le_rfl j.2).2.theta) (P j)

variable {W M t}

theorem pure_core (hP : GlobalTheory.Published.CuspRapidDecay) {M₀ : Vol G} (h₀ : M₀.IsRow) (hM : M.Is t) {ρ : RealMatch W}
    (hS : CuspStep W M ρ t) {e : AE D} (he : IsIdemSum e (locPl G t)) (φ d : SchRow G × SchDown G t)
    (hr : ∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (φ.1 i) (d.1 i))
    (hd : ∀ j : Fin D.R.m, IsLocVec W (.mu t D.R.m j) e (ρ.vT D.R.m j) (φ.2 j) (d.2 j)) (P : PolRow G × PolDown G)
    {F : Fn G (.grid 0 D.R.m)} (hF : IsCuspListed W.θ (.grid 0 D.R.m) F) {u : Fn G (.top 0)} (hu : GlobalTheory.Unf.IsContAut _ u) :
    IsCuspListed W.θ (.grid D.R.m D.R.m) (rowLift W M P.1 d.1 F) ∧
      IsCuspListed W.θ (.grid D.R.m 0) (liftP W M (oppPath t D.R.m) (oppPure W t P d) F) ∧
      (chain G W t hM).Iter (oppPer W hM P d u F) (Bplus W M₀ u (liftP W M (oppPath t D.R.m) (oppPure W t P d) F)) := by
  have hrow : IsCuspListed W.θ (.grid D.R.m D.R.m) (rowLift W M P.1 d.1 F) := by
    have H := GlobalTheory.ChainHyp.row_cusp hS he hF D.R.m le_rfl _ _
      (rowFam (S := fun a => PolF D (G.pT a.pair).rank (G.pS a.pair).rank) D.R.m D.R.m P.1)
      ((GlobalTheory.OppConv.vecAll_row ρ e _ _ φ.1 d.1).2 hr)
    rw [GlobalTheory.OppConv.zip_row] at H
    exact H
  have hz : downPure W t P.2 d.2 = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) (downFam t D.R.m D.R.m d.2)
      (downFam (S := fun a => PolF D (G.pT a.pair).rank (G.pS a.pair).rank) t D.R.m D.R.m P.2) :=
    (GlobalTheory.OppConv.zip_down (fun a (f : Sch G a) (Q : PolF D (G.pT a.pair).rank (G.pS a.pair).rank) => W.fock a.pair f Q)
      t D.R.m D.R.m d.2 P.2).symm
  have hv := (GlobalTheory.OppConv.vecAll_down ρ e t _ _ φ.2 d.2).2 hd
  have hc := GlobalTheory.ChainHyp.chain_props hP G W W.θ_is t hM (downPure W t P.2 d.2) _ hrow (fun k hk F' hF' => by
    rw [hz, GlobalTheory.ChainHyp.getD_zip]
    exact (hS (.down t D.R.m k) (Or.inr ⟨D.R.m, k, le_rfl, hk, rfl⟩) e he _ _
      (GlobalTheory.ChainHyp.getD_loc ρ e t _ _ _ _ hv k hk) _ F' hF').2) _ 0 top_idx (topVN hM)
  have hdn := GlobalTheory.RowChainDown.chain_down_eq_liftP G W t M hM (downPure W t P.2 d.2) (rowLift W M P.1 d.1 F)
  have hc1 : IsCuspListed W.θ (.grid D.R.m 0)
      ((chain G W t hM).down (chainData G W t hM (downPure W t P.2 d.2)) (rowLift W M P.1 d.1 F)) := hc.1
  rw [pathLift_oppositePure, ← hdn]
  refine ⟨hrow, hc1, ?_⟩
  have hB := (bplus_indep W h₀ hM u _ hu.1 hc1.1.toIsAutFun.left).trans (TopPer.bplus_eq_topLev_per G W t M hM u _)
  rw [hB]
  exact iter_colPer W hM _ (allTheta_downPure W t ρ e φ.2 d.2 hd P.2) _
    ⟨hrow.1.toIsAutFun.left, hrow.1.toIsAutFun.cont⟩ u hu hc.2

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.FlipRun GlobalTheory.RowUnf GlobalTheory.RowVal

theorem nIter_meas_congr {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
    {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) {μ μ' : ∀ i, Measure (H i)} {q : (∀ i, H i) → ℂ} :
    ∀ (l : List ι) (h : ∀ i, H i) (z : ℂ), (∀ i ∈ l, μ i = μ' i) → NIter ρ μ q l h z → NIter ρ μ' q l h z
  | [], _, _, _, hz => hz
  | i :: l, _, _, e, ⟨f, hf, hr⟩ => ⟨f, e i (by simp) ▸ hf, fun g =>
      nIter_meas_congr ρ l _ _ (fun k hk => e k (List.mem_cons_of_mem _ hk)) (hr g)⟩

theorem exists_haar_heq {H : Type} [Group H] [TopologicalSpace H] [MeasurableSpace H] {R R' : Subgroup H} (e : R = R')
    (ρ' : Measure R') (h : ρ'.IsHaarMeasure) : ∃ ρ : Measure R, ρ.IsHaarMeasure ∧ HEq ρ ρ' := by
  subst e
  exact ⟨ρ', h, HEq.rfl⟩

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem exists_vol_top (j : ℕ) : ∃ v : GlobalTheory.Unf.Vol (G.V (.top j)), j ≤ D.R.m → ∀ t (M : Vol G), M.Is t → M.ν (.top j) = v.μ := by
  by_cases h : j ≤ D.R.m ∧ ∃ t, ∃ M : Vol G, M.Is t
  · obtain ⟨hj, t₀, M₀, h₀⟩ := h
    exact ⟨volAt h₀ (.top j) hj, fun _ t M hM => (vol_row_top_indep G t t₀ M M₀ hM h₀).2 j hj⟩
  · exact ⟨(GlobalTheory.Unf.Inhab.nonempty_vol _).some, fun hj t M hM => absurd ⟨hj, t, M, hM⟩ h⟩

theorem exists_vol_row (j : ℕ) : ∃ v : GlobalTheory.Unf.Vol (G.V (.grid D.R.m j)),
    1 ≤ j → j ≤ D.R.m → ∀ t (M : Vol G), M.Is t → M.ν (.grid D.R.m j) = v.μ := by
  by_cases h : 1 ≤ j ∧ j ≤ D.R.m ∧ ∃ t, ∃ M : Vol G, M.Is t
  · obtain ⟨h1, hj, t₀, M₀, h₀⟩ := h
    exact ⟨volAt h₀ (.grid D.R.m j) ⟨le_rfl, hj⟩, fun _ _ t M hM => (vol_row_top_indep G t t₀ M M₀ hM h₀).1 j h1 hj⟩
  · exact ⟨(GlobalTheory.Unf.Inhab.nonempty_vol _).some, fun h1 hj t M hM => absurd ⟨h1, hj, t, M, hM⟩ h⟩

theorem exists_rowMeas (j : ℕ) : ∃ ρ : Measure (rowGrp G j), (j < D.R.m → ρ.IsHaarMeasure) ∧ ∀ t (M : Vol G) (hM : M.Is t),
    (∀ σ (hj : j + 2 * σ + 1 = D.R.m), HEq ρ (jacAt G hM j σ hj).μR) ∧
      ∀ σ (hj : j + 2 * σ + 2 = D.R.m), HEq ρ (besAt G hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).μR := by
  obtain ⟨v, hv⟩ := exists_vol_top G j
  by_cases h : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
  · let J : GlobalTheory.Unf.JacLev D ((D.R.m - 1 - j) / 2) :=
      ⟨G.V (.grid D.R.m j), G.V (.top j), rowJac G j (by omega) _ (by omega), cocpt_top G (by omega), v,
        (GlobalTheory.Unf.Inhab.nonempty_volN _).some⟩
    have e : rowGrp G j = jacGrp J.d := dif_pos h
    obtain ⟨ρ, h1, h2⟩ := exists_haar_heq e J.μR (GlobalTheory.QuotZero.jac_haar_inv J).2.1
    refine ⟨ρ, fun _ => h1, fun t M hM => ⟨fun σ hj => ?_, fun σ hj => by omega⟩⟩
    obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
    refine h2.trans (heq_of_eq ?_)
    show semiMeas _ _ v.μ _ = semiMeas _ _ (M.ν (.top j)) _
    rw [hv (by omega) t M hM]
    rfl
  by_cases h' : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m
  · let B : GlobalTheory.Unf.BesLev D ((D.R.m - 2 - j) / 2) :=
      ⟨G.V (.grid D.R.m j), _, G.V (.top j), GlobalTheory.SeeSaw.Model.nLine D, besDecAt G j _ h', GlobalTheory.OrthSumExists.orthDecHsum D _ _,
        fun _ => D.host.xi0 ^ ((D.R.m - 2 - j) / 2),
        GlobalTheory.SeeSaw.Model.isLineVec_nLine (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), cocpt_top G (by omega), v,
        (GlobalTheory.Unf.Inhab.nonempty_volN _).some⟩
    have e : rowGrp G j = besGrp B.d B.o := (dif_neg h).trans (dif_pos h')
    obtain ⟨ρ, h1, h2⟩ := exists_haar_heq e B.μR (GlobalTheory.QuotZero.bes_haar_inv B).2.1
    refine ⟨ρ, fun _ => h1, fun t M hM => ⟨fun σ hj => by omega, fun σ hj => ?_⟩⟩
    obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
    refine h2.trans (heq_of_eq ?_)
    show semiMeas _ _ v.μ _ = semiMeas _ _ (M.ν (.top j)) _
    rw [hv (by omega) t M hM]
    rfl
  · exact ⟨0, fun _ => by omega, fun t M hM => ⟨fun σ hj => by omega, fun σ hj => by omega⟩⟩

theorem mem_idx {j : ℕ} (hj : j ∈ idx D) : 1 ≤ j ∧ j < D.R.m := by
  simp only [idx, List.mem_range'_1] at hj
  omega

theorem iterAt_big : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch := by
  intro hP hL
  obtain ⟨c0, h0⟩ := (GlobalTheory.T.cuspidal_flip_on_volumes hL hP).and ((GlobalTheory.EndCusp.formTop_isCuspListed hP).and GlobalTheory.RowClaim.colFn_cont_left)
  refine ⟨c0, fun ε CF hC => ?_⟩
  obtain ⟨x0, hx⟩ := h0 ε CF hC
  refine ⟨x0, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R Fc hS ch hch hsc => ?_⟩
  obtain ⟨hstep, htop, hcol⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R Fc hS ch hch hsc
  choose ρ hρ hρ' using exists_rowMeas ch.G
  choose v hv using exists_vol_row ch.G
  refine ⟨ρ, fun j => (v j).μ, fun j hj => ⟨hρ j (mem_idx hj).2, (v j).haar⟩, ?_⟩
  intro t a τ hτ M hM P y
  obtain ⟨e, he, φm, hw, -⟩ := hτ
  have hu : GlobalTheory.Unf.IsContAut _ (colFn ch a) := ⟨(hcol a).2, (hcol a).1⟩
  have core : ∀ d ∈ τ.support,
      BplusConv ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) ∧
      NIter ρ (fun j => (v j).μ) (fun h => per ch.W M t (conAt ch.W hM (fockD ch.W t d.2 P.2) h) d.1 P.1 (colFn ch a) (formTop ch t y))
        (idx D) 1 (Bplus ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y))) := by
    intro d hd
    have h2 := hw d hd
    obtain ⟨-, h1, h3⟩ := pure_core hP.cuspRapidDecay hch.vol hM (hstep t M hM) he (φm d) d h2.1 h2.2 P (htop t y) hu
    refine ⟨GlobalTheory.RowBplus.bplusConv_col ch.W ch.M hch.vol ch.ξ (ch.col a) (col_mem ch a) _ h1.1.toIsAutFun, ?_⟩
    exact nIter_meas_congr ρ _ _ _ (fun j hj => hv j (mem_idx hj).1 (mem_idx hj).2.le t M hM)
      (nIter_conAt_of_colPer ch.G ch.W t hM (fockD ch.W t d.2 P.2) _ _ _ h3 ρ (fun j => (hρ' j t M hM).1)
        fun j => (hρ' j t M hM).2)
  have e1 : liftT ch.W M (oppPath t D.R.m) (oppTens ch.W t (Finsupp.single P 1) τ) (formTop ch t y) =
      ∑ d ∈ τ.support, τ d • liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y) := by
    rw [GlobalTheory.RowVal.liftT_oppTens, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same,
      one_smul]
  have e2 : lhs ch t M (Finsupp.single P 1) τ a y = ∑ d ∈ τ.support,
      τ d * Bplus ch.W ch.M (colFn ch a) (liftP ch.W M (oppPath t D.R.m) (oppPure ch.W t P d) (formTop ch t y)) := by
    rw [lhs, e1, (bplus_sum_right ch.W ch.M (colFn ch a) τ.support _
      fun d hd => (bplus_smul_right ch.W ch.M (τ d) (core d hd).1).1).2]
    exact Finset.sum_congr rfl fun d hd => (bplus_smul_right ch.W ch.M _ (core d hd).1).2
  rw [e2]
  exact (niter_lin_congr _ _ _ ρ _ (idx D) 1).1 _ τ.support τ _ _ fun d hd => (core d hd).2

theorem iterAt_linAt : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → Big fun ch => IterAt ch ∧ LinAt ch :=
  fun hP hL => (iterAt_big hP hL).and (linAt_big hP hL)

end GlobalTheory.RowChain

end
