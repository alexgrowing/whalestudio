import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitSupportedRepFiniteUnitaryClassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGoodStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BaseClassSum

variable {D : D7} {S T : HSp D}

theorem series_move {B : Base S T} (hB : B.Good) (hS : S.SigOK) {t : Twist D Circle} (ht : t.Good) (hQ : B.admitted t.Q)
    {ω : PairRep S T} (hω : B.IsWeil t.chi ω) {h h' : GA D S} (hh : h ∈ GfC S) (hh' : h' ∈ GfC S) (γ : GQ S) (k : B.levJ t)
    (e : finPt S h = Bridge.ratF S γ * finPt S h' * (k : Bridge.Gf S)) (P : PolF D T.rank S.rank) :
    series B.F ω (B.vecFlat t) h P =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • series B.F ω (B.vecFlat t) h' (B.act ((γ⁻¹ : GQ S) : GA D S) P) := by
  obtain ⟨hsplit, hcomm, htriv, -, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨x, hx⟩ := (k : Bridge.Gf S).2
  obtain ⟨kk, hkk, -, -, -, hfk⟩ := GlobalTheory.LiftUnfold.exists_fin_mul_real S x
  have hkk' : finPt S kk = (k : Bridge.Gf S) := hfk.trans (Subtype.ext hx)
  obtain ⟨ga, hga, gf, hgf, hγ⟩ := hsplit (γ : GA D S)
  have hfγ : Bridge.ratF S γ = finPt S gf := by
    change finPt S (γ : GA D S) = _
    rw [hγ]
    dsimp only [finPt]
    rw [map_mul]
    have : (finHom S).rangeRestrict ga = 1 := Subtype.ext (MonoidHom.mem_ker.1 hga)
    rw [this, one_mul]
  have eh : h = (γ : GA D S) * h' * ga⁻¹ * kk := by
    have eg : gf = (γ : GA D S) * ga⁻¹ := by
      rw [hγ, hcomm ga hga gf hgf, mul_inv_cancel_right]
    have e1 : h = gf * h' * kk := by
      set y := (gf * h' * kk)⁻¹ * h with hy
      have hyf : y ∈ GfC S := mul_mem (inv_mem (mul_mem (mul_mem hgf hh') hkk)) hh
      have hyi : y ∈ GinfC S := by
        have : finPt S y = 1 := by
          rw [hy]
          dsimp only [finPt] at hkk' hfγ e ⊢
          rw [map_mul, map_inv, map_mul, map_mul, hkk', ← hfγ]
          change _ * ((finHom S).rangeRestrict h) = 1
          rw [e]
          exact inv_mul_cancel _
        exact MonoidHom.mem_ker.2 (congrArg Subtype.val this)
      have := htriv y hyi hyf
      rw [hy, inv_mul_eq_one] at this
      exact this.symm
    rw [e1, eg, mul_assoc (γ : GA D S) ga⁻¹ h', hcomm ga⁻¹ (inv_mem hga) h' hh', ← mul_assoc]
  have hact : B.act ((γ⁻¹ : GQ S) : GA D S) = B.act ga⁻¹ := by
    have hr : GlobalTheory.ExportSeries.realGL B.F.θ S gf = 1 := by
      funext τ
      show Formalism.UG.bc (B.F.θ τ) (infHom S gf) = 1
      rw [MonoidHom.mem_ker.1 hgf, map_one]
    rw [Base.act, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_inv, hγ, _root_.mul_inv_rev, map_mul, map_inv _ gf, hr,
      inv_one, one_mul]
  have hJ : finPt S kk ∈ B.levJ t := hkk' ▸ k.2
  have hθf : ∀ P, IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat t) P) := Base.isThetaFunO_fock_vecAt hB hQ _
  have hk : ω (kk, 1) (B.F.fock (B.vecFlat t) P) = ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat t) P := by
    have h1 := GlobalTheory.ExportSeries.DualType.dual_type_fock hB hS ht hQ hω hkk hJ P
    have e2 : ((B.levLam t ⟨_, hJ⟩ : ℂˣ) : ℂ) = ((B.levLam t k : ℂˣ) : ℂ) :=
      congrArg (fun z : B.levJ t => ((B.levLam t z : ℂˣ) : ℂ)) (Subtype.ext hkk')
    rw [← e2]
    exact h1
  have ha : ω (ga⁻¹, 1) (B.F.fock (B.vecFlat t) P) = B.F.fock (B.vecFlat t) (B.act ga⁻¹ P) :=
    GlobalTheory.RealFockAction.om_fock_vecAt D S T B t ω t.Q _ hB ht hQ hω ga⁻¹ (inv_mem hga) P
  have ep : ∀ g : GA D T, (((γ : GA D S) * h' * ga⁻¹ * kk, g) : GA D S × GA D T) =
      ((γ : GA D S), 1) * ((h', g) * ((ga⁻¹, 1) * (kk, 1))) := fun g => by
    ext <;> simp [mul_assoc]
  have key : ∀ g : GA D T, ω (h, g) (B.F.fock (B.vecFlat t) P) 0 =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ * ω (h', g) (B.F.fock (B.vecFlat t) (B.act ga⁻¹ P)) 0 := fun g => by
    rw [eh, ep g, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hk, map_smul, ha,
      map_smul, map_smul, Pi.smul_apply, hω.om_aut _ γ.2 1 (one_mem _) _ (hω.om_pres _ _ (hθf _)), smul_eq_mul]
  refine funext fun g => ?_
  rw [Pi.smul_apply, smul_eq_mul, hact]
  exact key g

theorem series_triv (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h P = ρ.theta i j b h P := by
  have key : ∀ t : Twist D Circle, t.Q = ∅ → t.chi = 1 →
      series (ρ.B i j b).F (ρ.om i j b t.chi) ((ρ.B i j b).vecFlat t) h P = ρ.theta i j b h P := by
    rintro ⟨_, _, r⟩ rfl rfl
    show series _ _ ((ρ.B i j b).vecAt ∅ _) h P = series _ _ (ρ.B i j b).vecBase h P
    rw [Base.vecAt_empty]
  exact key _ (half_empty _) (charOf_one _ _)

theorem term_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank} (hF : F ∈ (ρ.B i j b).formsC (ρ.tw i b 0 ∅ 1))
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h (F (finPt _ h)) ∈
      Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hB := hρ.base i j b
  have hω := hρ.weil i j b _ hg
  obtain ⟨γ, s, h', k, hs, hoff, hh', hsupp, e⟩ := GlobalTheory.T.exists_split_supported_rep_finite_unitary_class D ρ hρ i j b h hh
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF).2 γ (finPt _ h') k
  have hval : F (finPt _ h') ∈ (ρ.B i j b).valSpace := ((ρ.B i j b).mem_formsC.1 hF).1 _
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e, hlaw, LinearMap.map_smul, series_move hB (D.sp.V_sig _) hg ha hω hh hh' γ k e, hinv, smul_smul,
    mul_inv_cancel₀ (Units.ne_zero _), one_smul, series_triv]

  have hspan : F (finPt _ h') ∈ Submodule.span ℂ (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) := by
    have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
      have h1 := hB.sig τ
      have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
      rw [← h1] at h2
      exact h2.le
    have hlat : Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt _ h')) :=
      Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg) hB.frame.sdS.1.span_eq_top _
    have h2 := (GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space D (Wc D j).rank (Vc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS _ (Formalism.L2.Host.embLL0 D) (labLL0 D)
      (ρ.eO i b).range ((ρ.B i j b).latAt (finPt _ h')) hB.wt hm (hρ.isCoefRing i b) hlat).2
    have h3 : (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) =
        (harmLat (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.eO i b).range (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS
          ((ρ.B i j b).latAt (finPt _ h')) : Set (PolF D (Wc D j).rank (Vc D j).rank)) := rfl
    rw [h3, h2]
    exact hval
  have hmap := Submodule.mem_map_of_mem (f := (ρ.B i j b).theta (ρ.om i j b 1) h') hspan
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨s, h', P, ⟨hs, hoff, hh', hsupp, hP⟩, rfl⟩

theorem sum_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank}
    (hF : F ∈ Submodule.span ℂ (ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))) :
    ρ.sum i j b 0 ∅ 1 F ∈ Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hc := hρ.classes i j b _ hg ha
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hF' := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
    rw [Setup.sum, Base.classSum_apply]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (term_mem_span hρ i j b hF'.1 (hc.fin c))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BaseClassSum

namespace GlobalTheory.TwInputs

theorem spanGood_of_sumOnto : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), ∀ i, SumOnto rd i → SpanGood rd i := by
  intro D ρ hρ rd i hS j b x hx
  obtain ⟨F, hF, e⟩ := hS j b x hx
  rw [e]
  exact GlobalTheory.BaseClassSum.sum_mem_span hρ i j b hF

end GlobalTheory.TwInputs
