import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralStripEqZeroOfRealModulationVanishingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUnfoldingIntegratedOverFamilyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointJacobiFunctionUnfoldedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselFlatMapEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedFunctionConvergesContinuousStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicStripSetMeasurableReadOnRealPartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeigStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExistStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDomaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFlatMapWeilRepresentationJointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLawsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.VanJac

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem isTh_const_mul {V V₀ W : HSp D} {ρ : ℕ} {d : HypDec V V₀ ρ} {x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E}
    {Th : GA D V → ℂ} (h : IsTh ψ d W x₀ Th) (c : ℂ) : IsTh ψ d W x₀ fun n => c * Th n where
  cont := continuous_const.mul h.cont
  left γ hγ hγ' n hn := by rw [h.left γ hγ hγ' n hn]
  cen a n hn := by rw [h.cen a n hn]; ring
  dep j a h1 h2 h3 := by
    obtain ⟨v, u, t, e1, e2, e3, e4, e5⟩ := h.dep j a h1 h2 h3
    exact ⟨v, u, t, e1, e2, e3, e4, fun n hn n' hn' => by rw [e5 n hn n' hn']; ring⟩

theorem fl_const_mul {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank)
    (vU : VolU D ρ) (Th : GA D V → ℂ) (c : ℂ) (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) :
    fl ψ d W v vb vU (fun n => c * Th n) x Ψ = c * fl ψ d W v vb vU Th x Ψ := by
  simp only [fl, flFun, mul_assoc, integral_const_mul]

theorem integrable_rapid {V : HSp D} (v : GlobalTheory.Unf.Vol V) {φ : GA D V → ℂ} (hφ : RapidDec V φ) (N : ℕ) :
    Integrable (fun y => ‖φ y‖ * quotHeight V y ^ N) (v.μ.restrict v.𝓕) := by
  have hfin : v.μ v.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V v.μ _ v.haar v.fund
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨C, hC⟩ := hφ.decay N
  refine Integrable.of_bound (hφ.continuous.norm.mul ((continuous_quotHeight V).pow N)).aestronglyMeasurable C
    (.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (quotHeight_pos V y).le N))]
  exact hC y

variable {σ : ℕ} {J : JacL D (σ + 1)} {B : BesL D σ}

def thJ (ψ : AddChar (AF D.host.F) ℂ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ) (n : GA D J.W) : ℂ :=
  star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)

def gen (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E)
    (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) : Gen ψ J.W J.W₀ B.V (σ + 1) (GA D J.W₀) where
  d := J.d
  χV := s.χV
  χW := s.χW
  om := s.om
  vS := s.vS
  vN := J.vN
  vb := vb
  vU := s.vU
  vW := s.vW
  x₀ := x₀
  m := J.v0.μ.restrict J.v0.𝓕
  g := id
  Th := fun h n => φ h * thJ ψ J B (omz (h, 1) Φ₀) n

theorem quasi_om {S L : HSp D} {χ χz : (AE D)ˣ →* Circle} {omz : Om S L} (hz : IsWeilDatumO ψ S L χ χz omz)
    {Φ₀ : WO S L → ℂ} (h₀ : IsThetaFunO ψ S L Φ₀) (h : GA D S) : GlobalTheory.Unf.FB.Quasi ψ S L (omz (h, 1) Φ₀) :=
  ⟨(hz.om_pres _ _ h₀).quasi, (GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ S L χ χz omz hz Φ₀ h₀).comp (Continuous.prodMk_right (h, 1))⟩

theorem gen_is (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) {x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E}
    (hb : IsBase B.V x₀) (hth : ∀ y, GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → IsTh ψ J.d B.V x₀ (thJ ψ J B y))
    {χ χz : (AE D)ˣ →* Circle} {omz : Om J.W₀ B.L} (hz : IsWeilDatumO ψ J.W₀ B.L χ χz omz) {φ : GA D J.W₀ → ℂ}
    (hφ : RapidDec J.W₀ φ) {Φ₀ : WO J.W₀ B.L → ℂ} (h₀ : IsThetaFunO ψ J.W₀ B.L Φ₀) : (gen s vb x₀ omz φ Φ₀).Is := by
  have hψ : IsCharAF D.host.F ψ := s.weil.std.1
  have hval : ∀ y n, thJ ψ J B y n = star (ψ (cenS J.d B.L (zEll B.L (σ + 1) B.ζ) n) *
      y (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)) * star (psiFlag ψ J.d n) := fun y n => by
    rw [thJ, GlobalTheory.Unf.FB.ThLaws.jacS_zero_apply]
  obtain ⟨b1, b2, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  haveI := J.v0.haar
  refine ⟨s.weil, hb, (inferInstance : SFinite (J.v0.μ.restrict J.v0.𝓕)), continuous_id,
    fun y => isTh_const_mul (hth _ (quasi_om hz h₀ y)) _, ?_, ?_⟩
  · change Continuous fun p : GA D J.W₀ × flagN J.d => φ p.1 * thJ ψ J B (omz (p.1, 1) Φ₀) p.2.1
    simp only [hval]
    have hn : Continuous fun p : GA D J.W₀ × flagN J.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have hj := (GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ χ χz omz hz Φ₀ h₀).comp
      ((continuous_fst.prodMk (continuous_const (y := (1 : GA D B.L)))).prodMk
        ((GlobalTheory.Unf.FB.ThLaws.continuous_ptS J.d B.L (zEll B.L (σ + 1) B.ζ)).comp hn))
    exact (hφ.continuous.comp continuous_fst).mul
      ((((hψ.1.comp ((GlobalTheory.Unf.FB.ThLaws.continuous_cenS _ _ _).comp hn)).mul hj).star).mul
        ((GlobalTheory.Unf.FB.ThLaws.continuous_psiFlag hψ.1 _).comp hn).star)
  · obtain ⟨C, A, hC⟩ := GlobalTheory.T.weilRepresentation_thetaFunction_sup_le_quotientHeight D ψ _ _ χ χz omz hz Φ₀ h₀
    refine ⟨fun y => ‖φ y‖ * (C * quotHeight J.W₀ y ^ A),
      (hφ.continuous.norm.mul (continuous_const.mul ((continuous_quotHeight _).pow A))).measurable, fun y n _ => ?_,
      fun k => ?_⟩
    · change ‖φ y * thJ ψ J B (omz (y, 1) Φ₀) n‖ ≤ _
      have h1 : ‖psiFlag ψ J.d n‖ = 1 := hψ.2.1 _
      rw [hval, norm_mul, norm_mul, norm_star, norm_star, norm_mul, hψ.2.1, h1, one_mul, mul_one]
      have h2 := hC y 1 (ptS J.d B.L (zEll B.L (σ + 1) B.ζ) n)
      rw [quotHeight_of_mem B.L (one_mem _), mul_one] at h2
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    · refine ((integrable_rapid J.v0 hφ (A + k)).const_mul C).congr (.of_forall fun y => ?_)
      change C * (‖φ y‖ * quotHeight J.W₀ y ^ (A + k)) = ‖φ y‖ * (C * quotHeight J.W₀ y ^ A) * quotHeight J.W₀ y ^ k
      ring

theorem gen_lhs (s : StFB ψ J B) (vb : VolM D (σ + 1) J.W₀.rank) (x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E)
    (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ) :
    (gen s vb x₀ omz φ Φ₀).lhs G Φ = J.per ψ B.ζ omz φ (s.lift G Φ) Φ₀ := by
  unfold Gen.lhs JacL.per fjSrc
  refine integral_congr_ae (.of_forall fun y => integral_congr_ae (.of_forall fun n => ?_))
  change φ y * thJ ψ J B (omz (y, 1) Φ₀) n.1 * s.lift G Φ (n.1 * J.d.emb0 y) = _
  simp only [fjSrcFun, thJ, thetaJS]
  ring

theorem handP_smul_om (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) (c : ℂ) (h₁ : GA D B.A) :
    handP s vL omz φ Φ₀ (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) 1 = c * handP s vL omz φ Φ₀ Ξ h₁ := by
  unfold handP
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (1, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
      one_mul]
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem handP_zero (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) (h₁ : GA D B.A) : handP s vL omz φ Φ₀ 0 h₁ = 0 := by
  simp [handP, contractT, thPair]

theorem handP_rat (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) {Ξ : WO J.W₀ B.V₀ → ℂ} (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) :
    handP s vL omz φ Φ₀ Ξ γ = handP s vL omz φ Φ₀ Ξ 1 := by
  unfold handP
  congr 1
  funext h₀
  have e := fun w => GlobalTheory.PairKer.om_emb s.weil₀ hΞ B.o hγ h₀ 1 w
  simp only [mul_one] at e
  simp only [contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, e]

def unf (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ) (h : GA D B.V) : ℂ :=
  G h * handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) 1

theorem om_mul_apply {S T : HSp D} (om : Om S T) (a a' : GA D S) (b b' : GA D T) (f : WO S T → ℂ) :
    om (a * a', b * b') f = om (a, b) (om (a', b') f) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem unf_bes (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L) (φ : GA D J.W₀ → ℂ)
    (Φ₀ : WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) {Φ : WO J.W B.V → ℂ} (hΦ : IsThetaFunO ψ J.W B.V Φ) (h : GA D B.V)
    (h₁ : GA D B.A) (n : flagN B.d) : unf s vL omz φ Φ₀ G Φ (n.1 * embA B.d B.o h₁ * h) =
      besFun ψ 1 B.d B.o B.ζ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G) h₁ n := by
  have c := GlobalTheory.T.jacobiToBesselFlatMap_equivariant D ψ σ J B s _ (s.weil.om_pres (1, h) _ hΦ) 1 n.1 n.2 h₁
  rw [← om_mul_apply, map_one, one_mul] at c
  unfold unf besFun rTrans
  rw [c, handP_smul_om]
  ring

theorem jacobiToBesselFlatMap_core_translate (s : StFB ψ J B) {Φ : WO J.W B.V → ℂ} (hΦ : IsThetaFunO ψ J.W B.V Φ) (h₀ : GA D J.W₀) (h : GA D B.V) :
    flFB s (s.om (J.d.emb0 h₀, h) Φ) = s.om₀ (h₀, B.o.emb (1, 1)) (flFB s (s.om (1, h) Φ)) := by
  have c := GlobalTheory.T.jacobiToBesselFlatMap_equivariant D ψ σ J B s _ (s.weil.om_pres (1, h) _ hΦ) h₀ 1 (one_mem _) 1
  rw [← om_mul_apply, map_one, mul_one, mul_one, one_mul,
    (GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _), star_one, one_smul] at c
  exact c

set_option maxHeartbeats 1000000 in

theorem unf_measurable (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank)
    {x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E} (hx : (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ))
    (hli : LinearIndependent D.host.E x₀.transpose)
    {χ χz : (AE D)ˣ →* Circle} {omz : Om J.W₀ B.L} (hz : IsWeilDatumO ψ J.W₀ B.L χ χz omz) {φ : GA D J.W₀ → ℂ}
    (hφ : Continuous φ) {Φ₀ : WO J.W₀ B.L → ℂ} (h₀ : IsThetaFunO ψ J.W₀ B.L Φ₀) {G : GA D B.V → ℂ} (hG : Continuous G)
    {Φ : WO J.W B.V → ℂ} (hΦ : IsThetaFunO ψ J.W B.V Φ) : Measurable (unf s vL omz φ Φ₀ G Φ) := by
  obtain ⟨b1, b2, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨vU⟩ := (GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.2 B.L.rank
  obtain ⟨sL, -⟩ := GlobalTheory.Unf.sFinite_vol D B.L.rank J.W₀.rank vL vU
  haveI := J.v0.haar
  haveI : BorelSpace (Mx D B.L.rank J.W₀.rank) := ⟨rfl⟩
  have hfl := GlobalTheory.T.continuous_flatMap_weilRepresentation_joint D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.χV s.χW s.om s.weil s.vU x₀ hli Φ hΦ
  rw [hx] at hfl
  let f : (GA D B.V × GA D J.W₀) × Mx D B.L.rank J.W₀.rank →
      (GA D J.W × GA D B.V) × Mx D J.W₀.rank σ × WO J.W₀ B.V₀ :=
    fun q => ((J.d.emb0 q.1.2, q.1.1), ((0 : Mx D J.W₀.rank σ), (B.o.resT J.W₀).symm (0, q.2)))
  have hf : Continuous f :=
    ((J.d.continuous_embed.comp (continuous_snd.comp continuous_fst)).prodMk
      (continuous_fst.comp continuous_fst)).prodMk (continuous_const.prodMk
        ((B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_snd)))
  have h1 := hfl.comp hf
  have h2 : Continuous fun q : (GA D B.V × GA D J.W₀) × Mx D B.L.rank J.W₀.rank => star (omz (q.1.2, 1) Φ₀ q.2) :=
    continuous_star.comp ((GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ χ χz omz hz Φ₀ h₀).comp
      (((continuous_snd.comp continuous_fst).prodMk continuous_const).prodMk continuous_snd))
  let K : (GA D B.V × GA D J.W₀) × Mx D B.L.rank J.W₀.rank → ℂ := fun q =>
    flFB s (s.om (J.d.emb0 q.1.2, q.1.1) Φ) ((B.o.resT J.W₀).symm (0, q.2)) * star (omz (q.1.2, 1) Φ₀ q.2)
  have hK : Continuous K := h1.mul h2
  haveI : SecondCountableTopology (GA D B.V × GA D J.W₀) := inferInstance
  haveI : OpensMeasurableSpace (GA D B.V × GA D J.W₀) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (GA D B.V × GA D J.W₀) (Mx D B.L.rank J.W₀.rank) :=
    secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace ((GA D B.V × GA D J.W₀) × Mx D B.L.rank J.W₀.rank) := Prod.opensMeasurableSpace
  have m1 : StronglyMeasurable fun p : GA D B.V × GA D J.W₀ => ∫ v in vL.𝓕, K (p, v) ∂vL.μ :=
    hK.measurable.stronglyMeasurable.integral_prod_right'
  have m2 : StronglyMeasurable fun p : GA D B.V × GA D J.W₀ => φ p.2 * ∫ v in vL.𝓕, K (p, v) ∂vL.μ :=
    (hφ.comp continuous_snd).measurable.stronglyMeasurable.mul m1
  have m3 : StronglyMeasurable fun h : GA D B.V => ∫ y in J.v0.𝓕, φ y * ∫ v in vL.𝓕, K ((h, y), v) ∂vL.μ ∂J.v0.μ :=
    m2.integral_prod_right' (ν := J.v0.μ.restrict J.v0.𝓕)
  have e : unf s vL omz φ Φ₀ G Φ =
      fun h => G h * ∫ y in J.v0.𝓕, φ y * ∫ v in vL.𝓕, K ((h, y), v) ∂vL.μ ∂J.v0.μ := by
    funext h
    simp only [unf, handP, K, jacobiToBesselFlatMap_core_translate s hΦ]
    rfl
  rw [e]
  exact hG.measurable.mul m3.measurable

set_option maxHeartbeats 1000000 in

theorem vanFB : ∀ D : D7, VanFB D := by
  intro D ψ σ J B s 𝒮 Γ₀ K hL vL χ χz omz hz φ G Φ₀ hφ hG h₀ hGK hvan Φ hΦ𝒮
  have hΦ := hL.theta Φ hΦ𝒮
  obtain ⟨x₀, hx, hb, hR, hy⟩ := GlobalTheory.T.fourierJacobiStep_basePoint_jacobiFunction_unfolded D ψ σ J B s
  obtain ⟨vb⟩ := (GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.1 (σ + 1) J.W₀.rank
  have ha : (gen s vb x₀ omz φ Φ₀).Is := gen_is s vb hb (fun y h => (hy y h).1) hz hφ h₀
  have hker : (gen s vb x₀ omz φ Φ₀).ker G Φ = unf s vL omz φ Φ₀ G Φ := by
    funext h
    change G h * ∫ y in J.v0.𝓕, fl ψ J.d B.V s.vS vb s.vU (fun n => φ y * thJ ψ J B (omz (y, 1) Φ₀) n) (rat x₀)
      (s.om (J.d.emb0 y, h) Φ) ∂J.v0.μ = _
    unfold unf handP
    congr 2
    funext y
    rw [fl_const_mul, ← jacobiToBesselFlatMap_core_translate s hΦ]
    exact congrArg (φ y * ·) ((hy _ (quasi_om hz h₀ y)).2 vb vL _ (s.weil.om_pres _ _ hΦ))
  obtain ⟨b1, b2, b3, b4, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨b1', b2', b3', b4', -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  obtain ⟨-, -, hfd⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D B.V (GQ B.V ⊓ besGrp B.d B.o) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  have hU := B.vN.unit
  have hHR : (semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν).IsHaarMeasure :=
    (GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L σ B.d B.o B.vN.ν B.vN.𝓝 hU).2.2 B.vA.μ B.vA.haar
  obtain ⟨𝓡, h𝓡, hint⟩ := GlobalTheory.T.semidirect_haar_measure_fundamental_domain D B.V B.A (flagN B.d) (embA B.d B.o) (BesSemi.continuous_embA B.d B.o)
    (GlobalTheory.Mem.TrueRecord.isClosed_NFlag B.V (isIsoSub_e B.d))
    (fun n hn h => by rw [embA_apply]; exact GlobalTheory.MixPer.Decomp.conj_mem B.d hn _)
    (fun n hn n' hn' h h' e => BesSemi.unique B.d B.o hn hn' e) (fun n hn h => BesSemi.rat_iff B.d B.o hn h)
    B.vA B.vN.ν B.vN.𝓝 hU.1 hU.2.1 hHR
  obtain ⟨hsplit, hinv, -⟩ := ((GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D B.V).2.2.2.2.2 B.V₀ σ B.d).2 B.A B.L B.o
  obtain ⟨-, hone, -, -, hdec, -⟩ := GlobalTheory.T.flag_unipotent_bessel_character_laws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1
  obtain ⟨habs, hcont⟩ := GlobalTheory.T.besselPeriod_handedFunction_converges_continuous D ψ σ J B s vL χ χz omz hz φ G Φ₀ Φ hφ hG h₀ hΦ
  have hmeas := unf_measurable s vL hx hb.1 hz hφ.continuous h₀ hG.continuous hΦ
  have hm : ∀ h : GA D B.V, Measurable fun g : GA D B.V => unf s vL omz φ Φ₀ G Φ (g * h) :=
    fun h => hmeas.comp (continuous_mul_right h).measurable
  have habs' : ∀ h : GA D B.V, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝
      fun h₁ n => unf s vL omz φ Φ₀ G Φ (n.1 * embA B.d B.o h₁ * h) := fun h => by
    simp only [unf_bes s vL omz φ Φ₀ G hΦ]
    exact habs h
  have hmean : ∀ h : GA D B.V, (∫ r : besGrp B.d B.o in 𝓡, unf s vL omz φ Φ₀ G Φ (r * h)
      ∂(semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν)) =
        B.per ψ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G) := fun h => by
    refine ((hint _ (hm h)).2 (habs' h)).trans ?_
    simp only [unf_bes s vL omz φ Φ₀ G hΦ]
    rfl
  have key := GlobalTheory.T.continuousMean_vanishing_on_strips_at_one D B.V s.vW (besGrp B.d B.o) K (GlobalTheory.BesClosed.besGrp_isClosed D B.V B.V₀ B.A B.L σ B.d B.o)
    hsplit hL.fin hL.cpt hL.opn _ hHR (hinv _ hHR) 𝓡 𝓑 h𝓡 h𝓑 (unf s vL omz φ Φ₀ G Φ) hmeas ?_ ?_
    (fun h => (hint _ (hm h)).1.2 (habs' h)) ?_ ?_ ?_ ?_
  · have e := hmean 1
    have e1 : s.om ((1 : GA D J.W), (1 : GA D B.V)) Φ = Φ := by rw [Prod.mk_one_one, map_one, Module.End.one_apply]
    have e2 : rTrans (1 : GA D B.V) G = G := funext fun g => by rw [rTrans, mul_one]
    rw [e1, e2] at e
    simp only [mul_one] at e
    exact e.symm.trans key
  · intro γ hγ h
    obtain ⟨hq, hbes⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨n, hn, h₁, rfl⟩ := (hdec γ).1 hbes
    obtain ⟨hnq, hhq⟩ := (BesSemi.rat_iff B.d B.o hn h₁).1 hq
    have hth : IsThetaFunO ψ J.W₀ B.V₀ (flFB s (s.om (1, h) Φ)) := by
      have t := (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU x₀ hb.1 0 _
        (s.weil.om_pres (1, h) _ hΦ)).2
      rw [hx] at t
      exact t
    refine (unf_bes s vL omz φ Φ₀ G hΦ h h₁ ⟨n, hn⟩).trans ?_
    simp only [besFun, rTrans, unf]
    rw [handP_rat s vL omz φ Φ₀ hth hhq, hone _ n hnq, hG.1 _ hq h, star_one, mul_one, mul_comm]
  · rw [← hker]
    exact (GlobalTheory.T.thetaLift_unfolding_integrated_over_family D ψ J.W J.W₀ B.V (σ + 1) (GA D J.W₀) _ ha G Φ hG hΦ 𝓑 h𝓑').2.1
  · exact hcont.congr fun h => (hmean h).symm
  · intro k hk g
    have e : s.om (1, g * k) Φ = s.om (1, g) Φ := by
      have := om_mul_apply s.om 1 1 g k Φ
      rwa [one_mul, hL.fix Φ hΦ𝒮 k hk] at this
    rw [unf, unf, e, hGK k hk]
  · intro h hh
    have hne : flFB s (s.om (1, h) Φ) ≠ 0 := fun h0 => hh (by rw [unf, h0, handP_zero, mul_zero])
    have t := hL.supp Φ hΦ𝒮 h hne
    rwa [← hx, hR] at t
  · intro C hC hCi
    have t1 := (GlobalTheory.T.adelicStripSet_measurable_read_on_realPart D B.V (σ + 1) x₀ hb C hC hCi).1
    have t2 := GlobalTheory.T.integral_strip_eq_zero_of_real_modulation_vanishing D ψ J.W J.W₀ B.V (σ + 1) (GA D J.W₀) _ ha G hG Φ hΦ (fun c hc => ?_) 𝓑 h𝓑' C hC hCi
    · rw [hker] at t2
      rw [← hR]
      exact ⟨t1, t2⟩
    · rw [gen_lhs]
      refine hvan _ (hL.real Φ hΦ𝒮 _ ?_)
      change (c ⬝ J.d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hc, Matrix.zero_mul]

end GlobalTheory.Asc.VanJac

end
