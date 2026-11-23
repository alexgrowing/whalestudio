import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLifts

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceLevelPf

variable {D : D7} {S T : HSp D}

theorem series_om_fin {B : Base S T} (hB : B.Good) {χS χT : (AE D)ˣ →* Circle} {ω : PairRep S T}
    (hω : IsWeilDatumO B.F.ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f) (h : GA D S)
    (P : PolF D T.rank S.rank) (g : GA D T) {κ : GA D T} (hκ : κ ∈ GfC T) :
    series B.F ω (ω (1, κ) f) h P g = series B.F ω f h P (g * κ) := by
  rw [series_apply, series_apply]
  have e : ((h, g * κ) : GA D S × GA D T) = (h, g) * (1, κ) := Prod.ext (mul_one h).symm rfl
  rw [e, map_mul, Module.End.mul_apply, Frame.fock, Frame.fock,
    GlobalTheory.OrientedHeis.om_fin_pureTensorO B.F.ψ S T χS χT ω hω B.F.θ hB.frame.vac.2.inf 1 (one_mem _) κ hκ _ _ _ _ f P hf]

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}

theorem rTup_datWp_val (x : GL (Fin (Wc D i).rank) (EAf D)) (PP : ↥(R.datWp i R.triv).Pg) (a b : Fin (R.datWp i R.triv).r) :
    (rTup (R.βW i) (R.datWp i R.triv) x PP).val a b =
      (redFn (R.βW i) PP.1 x).val (Fin.castLE (R.datWp i R.triv).hr a) (Fin.castLE (R.datWp i R.triv).hr b) := by
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hm : redFn (R.βW i) PP.1 x ∈ blockTri (blk2 (R.datWp i R.triv).r) := by
    refine mem_blockTri.2 fun c d hcd => ?_
    have hc : c.val < (R.datWp i R.triv).r := lt_of_lt_of_eq c.2 rW
    have e : blk2 (R.datWp i R.triv).r c = 0 := if_pos hc
    exact absurd (lt_of_lt_of_eq hcd e) (Nat.not_lt_zero _)
  unfold rTup
  rw [upper_block_val_submatrix _ hm]
  rfl

theorem red_of_rTup (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) (x : GL (Fin (Wc D i).rank) (EAf D))
    (hx : rTup (R.βW i) (R.datWp i R.triv) x = R.eG g) : ∀ PP : ↥B.G.Pg, e g PP = redFn B.F.βT PP.1 x := by
  intro PP
  have hP : PP.1 ∈ R.Pg := hB.Pg ▸ PP.2
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h1 := congrArg (fun y : G0 (R.datWp i R.triv).Pg (R.datWp i R.triv).r => (y ⟨PP.1, hP⟩).val (Fin.cast (rank_Wc i) a)
    (Fin.cast (rank_Wc i) c)) hx
  simp only at h1
  rw [rTup_datWp_val] at h1
  rw [hent g PP.1 PP.2 hP a c]
  exact h1.symm.trans (by rw [hB.βT]; rfl)

theorem rTup_of_red (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) (x : GL (Fin (Wc D i).rank) (EAf D))
    (hx : ∀ PP : ↥B.G.Pg, e g PP = redFn B.F.βT PP.1 x) : rTup (R.βW i) (R.datWp i R.triv) x = R.eG g := by
  funext PP
  have hP : PP.1 ∈ B.G.Pg := hB.Pg ▸ PP.2
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h1 := hent g PP.1 hP PP.2 (Fin.cast (rank_Wc i).symm a) (Fin.cast (rank_Wc i).symm c)
  rw [hx ⟨PP.1, hP⟩, hB.βT] at h1
  rw [rTup_datWp_val]
  exact h1

theorem lifts_of_datWp (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) {g : G} {κ : GA D (Wc D i)}
    (hκ : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ) : GlobalTheory.ExportType.Lifts B (e g) κ :=
  ⟨hκ.1, hB.βT ▸ parLev_St hκ.2.1, red_of_rTup hB e hent g _ hκ.2.2⟩

theorem exists_lift_datWp (hB0 : B.Good) (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) :
    ∃ κ, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ := by
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.TypeSupportLift.exists_lift_supp B hB0 (e g)
  have h1 := GlobalTheory.FlatVecSum.levelLift_isLift_principalLevelDatum_realisation hB hκ
  rw [rTup_of_red hB e hent g _ (GlobalTheory.ExportType.lifts_of_isLiftG0 hκ).red] at h1
  exact ⟨κ, h1⟩

end Real

theorem traceLevel : GlobalTheory.BaseCmp.TraceLevel := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i B hB hBo U ψ e hent hU hchi ω hω hh P
  classical
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  have hlift := fun g => exists_lift_datWp hB hBo e hent g
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (GlobalTheory.FlatVecSum.princ B).vecBase :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) (Base.admissible_empty_of_good (GlobalTheory.FlatVecSum.princ_good hB)) _)
      hB.frame.vac.2.theta
  have hsum : B.vecBase = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) •
      ω (1, (hlift (e.symm p)).choose) (GlobalTheory.FlatVecSum.princ B).vecBase := by
    have := GlobalTheory.FlatVecSum.vecFlat_eq_sum_princ hB (D.sp.V_sig _) (Twist.triv_good splitSet_empty) (Base.admissible_empty_of_good hB)
      (ω := ω) hω (fun p => (hlift (e.symm p)).choose) (fun p => by
        have := lifts_of_datWp hBo e hent (hlift (e.symm p)).choose_spec
        rwa [MulEquiv.apply_symm_apply] at this)
    rwa [Base.vecFlat_triv, Base.vecFlat_triv] at this
  funext x
  have hL : levelTrace R i U ψ ((GlobalTheory.FlatVecSum.princ B).theta ω hh P) x =
      ∑ g, (if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0) *
        series B.F ω (GlobalTheory.FlatVecSum.princ B).vecBase hh P (x * (hlift g).choose) := by
    unfold levelTrace gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    show Lev.actG0 _ _ _ _ _ x = _
    rw [Lev.actG0]
    split_ifs with hk
    · rw [GlobalTheory.CuspMult.EqCut.levChi_flag rfl rfl, inv_one]
      exact one_mul _
    · exact absurd (hlift g) hk
  have hR : B.theta ω hh P x = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) *
      series B.F ω (GlobalTheory.FlatVecSum.princ B).vecBase hh P (x * (hlift (e.symm p)).choose) := by
    rw [Base.theta, hsum, GlobalTheory.SpecFac.series_sum hB ω _ _ _ (fun p _ => hW.om_pres _ _ hfθ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [series_om_fin hB hW hfθ hh P x (hlift (e.symm p)).choose_spec.1]
  rw [hL, hR]
  symm
  refine Fintype.sum_of_injective (fun p : B.G.P.H => e.symm p) (fun p q hpq => Subtype.ext (e.symm.injective hpq)) _ _
    (fun g hg => ?_) (fun p => ?_)
  · rw [dif_neg, zero_mul]
    intro hgU
    exact hg ⟨⟨e g, (hU g).2 hgU⟩, e.symm_apply_apply g⟩
  · have hp : e.symm p ∈ U := (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact p.2)
    have key : ((B.G.P.chi p : ℂˣ) : ℂ) = D.what₂.embLL ((ψ ⟨e.symm p, hp⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hp' : e (e.symm p) ∈ B.G.P.H := by rw [MulEquiv.apply_symm_apply]; exact p.2
      have := hchi ⟨e.symm p, hp⟩ hp'
      have hpe : (⟨e (e.symm p), hp'⟩ : B.G.P.H) = p := Subtype.ext (e.apply_symm_apply p)
      rw [hpe] at this
      exact this
    rw [dif_pos hp, Units.val_inv_eq_inv_val, key, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.TraceLevelPf
