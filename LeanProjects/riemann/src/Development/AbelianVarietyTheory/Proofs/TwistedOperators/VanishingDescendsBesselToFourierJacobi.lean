import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDomaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiKernelLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselMeanPeriodConvergesContinuousStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToJacobiFlatMapEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelUnfoldingCharacterAndFlatMapStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralStripEqZeroOfRealModulationVanishingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUnfoldingIntegratedOverFamilyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.VanBessel

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesL D ρ} {J : JacL D ρ} (s : StBF ψ B J)

theorem isTh_const_mul {V V₀ W : HSp D} {d : HypDec V V₀ ρ} {x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E} {Th : GA D V → ℂ}
    (h : IsTh ψ d W x₀ Th) (c : ℂ) : IsTh ψ d W x₀ fun n => c * Th n := by
  refine ⟨continuous_const.mul h.cont, fun γ hγ hN n hn => by rw [h.left γ hγ hN n hn],
    fun c' n hn => by rw [h.cen c' n hn]; ring, fun j a h1 h2 h3 => ?_⟩
  obtain ⟨v, u, c', e1, e2, e3, e4, e5⟩ := h.dep j a h1 h2 h3
  exact ⟨v, u, c', e1, e2, e3, e4, fun n hn n' hn' => by rw [e5 n hn n' hn']; ring⟩

theorem fl_const_mul {V V₀ W : HSp D} (d : HypDec V V₀ ρ) (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ)
    (Th : GA D V → ℂ) (c : ℂ) (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) :
    fl ψ d W v vb vU (fun n => c * Th n) x Ψ = c * fl ψ d W v vb vU Th x Ψ := by
  simp only [fl, flFun, mul_assoc, integral_const_mul]

def gen (φ : GA D B.A → ℂ) : Gen ψ B.V B.V₀ J.W ρ (GA D B.A) where
  d := B.d
  χV := s.χV
  χW := s.χW
  om := s.om
  vS := s.vS
  vN := B.vN
  vb := s.vT
  vU := s.vU
  vW := s.vW
  x₀ := J.d.e
  m := B.vA.μ.restrict B.vA.𝓕
  g := fun h₀ => B.o.emb (h₀, 1)
  Th := fun h₀ n => φ h₀ * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)

theorem gen_is {φ : GA D B.A → ℂ} (hφ : RapidDec B.A φ) : (gen s φ).Is := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  haveI : BorelSpace (GA D B.A) := ⟨rfl⟩
  haveI := B.vA.haar
  have hTh := (GlobalTheory.T.besselLevel_unfolding_character_and_flatMap D ψ ρ B J s).1
  have hg : Continuous fun h₀ : GA D B.A => B.o.emb (h₀, 1) :=
    B.o.continuous_emb.comp (continuous_id.prodMk continuous_const)
  refine ⟨s.weil, (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1, inferInstanceAs (SFinite (B.vA.μ.restrict B.vA.𝓕)), hg,
    fun y => isTh_const_mul hTh (φ y), (hφ.2.1.comp continuous_fst).mul (hTh.cont.comp continuous_snd),
    fun y => ‖φ y‖, hφ.2.1.norm.measurable, fun y n _ => ?_, fun k => ?_⟩
  · change ‖φ y * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)‖ ≤ ‖φ y‖
    rw [norm_mul, norm_star, psiBes, psiE, s.weil.std.1.2.1, mul_one]
  · obtain ⟨C, a, hC⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
    have hq : Continuous fun y : GA D B.A => quotHeight B.V₀ (B.o.emb (y, 1)) ^ k :=
      ((continuous_quotHeight B.V₀).comp hg).pow k
    have h := hφ.integrableOn_mul_of_le B.vA.haar B.vA.fund
      (f := fun y => ((quotHeight B.V₀ (B.o.emb (y, 1)) ^ k : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hq).measurable.aestronglyMeasurable (C := C ^ k) (A := a * k) fun y => by
        rw [Complex.norm_real, Real.norm_of_nonneg (pow_pos (quotHeight_pos _ _) k).le, pow_mul, ← mul_pow]
        exact pow_le_pow_left₀ (quotHeight_pos _ _).le (hC y).2 k
    refine (Integrable.norm h).congr (Filter.Eventually.of_forall fun y => ?_)
    change ‖((quotHeight B.V₀ (B.o.emb (y, 1)) ^ k : ℝ) : ℂ) * φ y‖ = ‖φ y‖ * quotHeight B.V₀ (B.o.emb (y, 1)) ^ k
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_pos (quotHeight_pos _ _) k).le, mul_comm]

theorem gen_lhs (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ) :
    (gen s φ).lhs G Φ = B.per ψ φ (s.lift G Φ) := by
  simp only [Gen.lhs, BesL.per, besPer, besFun]
  refine congrArg _ (funext fun h₀ => congrArg _ (funext fun n => ?_))
  change φ h₀ * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1) * s.lift G Φ (n.1 * embA B.d B.o h₀) = _
  ring

theorem gen_ker (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) {Φ : WO B.V J.W → ℂ} (hΦ : IsThetaFunO ψ B.V J.W Φ) :
    (gen s φ).ker G Φ = fun h => G h * ∫ h₀ in B.vA.𝓕, φ h₀ * flBF s (s.om (embA B.d B.o h₀, h) Φ) 0 ∂B.vA.μ := by
  funext h
  refine congrArg (G h * ·) (congrArg _ (funext fun h₀ => ?_))
  change fl ψ B.d J.W s.vS s.vT s.vU (fun n => φ h₀ * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d)
    (s.om (embA B.d B.o h₀, h) Φ) = _
  rw [fl_const_mul, (GlobalTheory.T.besselLevel_unfolding_character_and_flatMap D ψ ρ B J s).2 _ (s.weil.om_pres _ _ hΦ)]

theorem flBF_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) : IsThetaFunO ψ B.V₀ J.W₀ (flBF s Ψ) :=
  (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e
    (GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).1.1 _ Ψ hΨ).2

theorem flBF_rat {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ : GA D J.W}
    (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d) : flBF s (s.om (1, γ) Ψ) 0 = flBF s Ψ 0 := by
  obtain ⟨n, hn, h', rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hγ.2
  obtain ⟨hnQ, hh'⟩ := ((GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d).2.2.2.2.2 n hn h').1 hγ.1
  have hψ := s.weil.std.1
  have hΞ := flBF_theta s hΨ
  have hy : yZero B.V₀ ρ (vecB B.o B.ζ) ∈ ratMx D B.V₀.rank ρ := neg_mem (GlobalTheory.UnfKer.zEll_rat _ _ _)
  rw [← map_one (embA B.d B.o), GlobalTheory.T.besselToJacobiFlatMap_equivariant D ψ ρ B J s Ψ hΨ 1 n hn h', psiFlag_eq,
    GlobalTheory.CharLaws.psiBes_rat ψ J.d hψ.2.2.1 1 0 hnQ,
    star_one, one_smul, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply, opA,
    GlobalTheory.UnfKer.jacT_rat hψ J.d B.V₀ hy hnQ (s.weil₀.om_pres _ _ hΞ), s.weil₀.om_aut 1 (one_mem _) h' hh' _ hΞ]

theorem om_om (g g' : GA D B.V) (h h' : GA D J.W) (Φ : WO B.V J.W → ℂ) :
    s.om (g * g', h * h') Φ = s.om (g, h) (s.om (g', h') Φ) := by
  rw [← Module.End.mul_apply, ← map_mul s.om, Prod.mk_mul_mk]

end GlobalTheory.Asc.VanBessel

namespace GlobalTheory.Asc

open VanBessel in

theorem vanBF : ∀ D : D7, VanBF D := by
  intro D ψ ρ B J s 𝒮 Γ₀ K hL φ G hφ hG hGK hvan Φ hΦ𝒮
  have hΦ := hL.theta Φ hΦ𝒮
  obtain ⟨hb, -, hx, hR, hemb, hrat⟩ := GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  haveI : BorelSpace (GA D B.A) := ⟨rfl⟩
  haveI : BorelSpace (GA D J.W) := ⟨rfl⟩
  haveI := B.vA.haar
  haveI := s.vW.haar
  have ha := gen_is s hφ
  obtain ⟨-, -, hfd⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D J.W (GQ J.W ⊓ jacGrp J.d) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  have h𝓑' := h𝓑
  rw [← hR] at h𝓑'
  have hint := (GlobalTheory.T.thetaLift_unfolding_integrated_over_family D ψ B.V B.V₀ J.W ρ (GA D B.A) (gen s φ) ha G Φ hG hΦ 𝓑 h𝓑').2.1
  have hcut := GlobalTheory.T.integral_strip_eq_zero_of_real_modulation_vanishing D ψ B.V B.V₀ J.W ρ (GA D B.A) (gen s φ) ha G hG Φ hΦ (fun c hc => by
    rw [gen_lhs]
    refine hvan _ (hL.real Φ hΦ𝒮 _ ?_)
    change (c ⬝ B.d.pY).map (finPart D) = 0
    have hm : (c ⬝ B.d.pY).map (finPart D) = c.map (finPart D) * (B.d.pY).map (finPart D) := Matrix.map_mul
    rw [hm, hc, Matrix.zero_mul]) 𝓑 h𝓑'
  rw [gen_ker s φ G hΦ] at hint hcut
  set f : GA D J.W → ℂ := fun h => G h * ∫ h₀ in B.vA.𝓕, φ h₀ * flBF s (s.om (embA B.d B.o h₀, h) Φ) 0 ∂B.vA.μ with hf

  have hm : Measurable f := by
    have hc := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hb.1 Φ hΦ
    have he : Continuous (embA B.d B.o) :=
      B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
    have hq : Continuous fun p : GA D J.W × GA D B.A =>
        (((embA B.d B.o p.2, p.1), yZero B.V₀ ρ (vecB B.o B.ζ), 0) :
          (GA D B.V × GA D J.W) × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      ((he.comp continuous_snd).prodMk continuous_fst).prodMk continuous_const
    have hF : Continuous fun p : GA D J.W × GA D B.A => flBF s (s.om (embA B.d B.o p.2, p.1) Φ) 0 := by
      refine (hc.comp hq).congr fun p => ?_
      rw [Function.comp_apply, ← hx]
      rfl
    have hK : Continuous fun p : GA D J.W × GA D B.A => φ p.2 * flBF s (s.om (embA B.d B.o p.2, p.1) Φ) 0 :=
      (hφ.2.1.comp continuous_snd).mul hF
    exact hG.2.1.measurable.mul
      (hK.measurable.stronglyMeasurable.integral_prod_right' (ν := B.vA.μ.restrict B.vA.𝓕)).measurable

  have hinv : ∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ g, f (γ * g) = f g := fun γ hγ g => by
    simp only [hf]
    rw [hG.1 γ hγ.1]
    refine congrArg (G g * ·) (congrArg _ (funext fun h₀ => ?_))
    rw [← one_mul (embA B.d B.o h₀), om_om, flBF_rat s (s.weil.om_pres _ _ hΦ) hγ, one_mul]

  have hval : ∀ h h' (n : flagN J.d), f (n.1 * J.d.emb0 h' * h) =
      fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)) h' n := fun h h' n => by
    simp only [hf]
    rw [fjAllFun, rTrans, mul_assoc (G _), ← integral_const_mul (star _)]
    refine congrArg (G _ * ·) (congrArg _ (funext fun h₀ => ?_))
    rw [← mul_one (embA B.d B.o h₀), om_om,
      GlobalTheory.T.besselToJacobiFlatMap_equivariant D ψ ρ B J s _ (s.weil.om_pres _ _ hΦ) h₀ n.1 n.2 h', Pi.smul_apply, smul_eq_mul, fjKer]
    ring

  obtain ⟨-, -, -, -, hconj, hinj, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  have hclN := (GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D J.W J.W₀ ρ J.d).1
  obtain ⟨⟨hRcl, hRhaar⟩, -⟩ := GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ (GlobalTheory.UnfBessel.zeroSp D) ρ J.d (GlobalTheory.UnfBessel.orthZero J.W₀)
    J.vN.ν J.vN.𝓝 J.vN.unit
  obtain ⟨hνh, h𝓝, -⟩ := J.vN.unit
  have hμR : (semiMeas (flagN J.d) J.d.emb0 J.v0.μ J.vN.ν).IsHaarMeasure := hRhaar J.v0.μ J.v0.haar
  obtain ⟨𝓡, h𝓡, hsem⟩ := GlobalTheory.T.semidirect_haar_measure_fundamental_domain D J.W J.W₀ (flagN J.d) J.d.emb0 hemb hclN hconj hinj hrat J.v0 J.vN.ν J.vN.𝓝
    hνh h𝓝 hμR
  obtain ⟨hsplit, hunim, -⟩ := ((GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D J.W).2.2.2.2.2 J.W₀ ρ J.d).1
  obtain ⟨habs, hTc⟩ := GlobalTheory.T.besselMean_period_converges_continuous D ψ ρ B J s φ G Φ hφ hG hΦ
  have hmeas : ∀ h, Measurable fun g => f (g * h) := fun h => hm.comp (measurable_mul_const h)
  have habs' : ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => f (n.1 * J.d.emb0 h' * h) := fun h => by
    simp only [hval]
    exact habs h
  have hfun : ∀ h, ∫ r in 𝓡, f ((r : GA D J.W) * h) ∂(semiMeas (flagN J.d) J.d.emb0 J.v0.μ J.vN.ν) =
      J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) := fun h => by
    refine ((hsem (fun g => f (g * h)) (hmeas h)).2 (habs' h)).trans ?_
    simp only [JacL.perAll, fjAll, hval]
  have key := GlobalTheory.T.continuousMean_vanishing_on_strips_at_one D J.W s.vW (jacGrp J.d) K hRcl hsplit hL.fin hL.cpt hL.opn _ hμR (hunim _ hμR) 𝓡 𝓑 h𝓡 h𝓑 f hm hinv
    hint (fun h => ((hsem (fun g => f (g * h)) (hmeas h)).1).2 (habs' h)) (hTc.congr fun h => (hfun h).symm)
    (fun k hk g => by
      simp only [hf]
      rw [hGK k hk]
      refine congrArg (G g * ·) (congrArg _ (funext fun h₀ => ?_))
      rw [← mul_one (embA B.d B.o h₀), om_om, hL.fix Φ hΦ𝒮 k hk, mul_one])
    (fun h hh => by
      rw [← hR, ← hx]
      refine hL.supp Φ hΦ𝒮 h fun h0 => hh ?_
      have h0' : flBF s (s.om (1, h) Φ) = 0 := h0
      have := hval h 1 1
      rw [map_one, OneMemClass.coe_one, one_mul, one_mul] at this
      rw [this, h0']
      simp only [fjAllFun, fjKer, opA, OneMemClass.coe_one, jacT_one, map_zero, id, Pi.zero_apply, mul_zero, integral_zero])
    (fun C hC hCi => by
      rw [← hR]
      exact ⟨(GlobalTheory.T.adelicStripSet_measurable_read_on_realPart D J.W ρ J.d.e hb C hC hCi).1, hcut C hC hCi⟩)
  have h1 := hfun 1
  simp only [mul_one] at h1
  rw [show rTrans 1 G = G from funext fun h => congrArg G (mul_one h), Prod.mk_one_one, map_one, Module.End.one_apply] at h1
  exact h1.symm.trans key

end GlobalTheory.Asc

end
