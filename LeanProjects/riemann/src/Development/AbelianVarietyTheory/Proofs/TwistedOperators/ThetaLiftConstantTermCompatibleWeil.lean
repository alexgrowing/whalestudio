import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelModerateGrowthWithSeminorms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFacGen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermsRationalUnipotentInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralThetaLiftTermSumNeTopStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadicaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaSeriesModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergTermsPermutedRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicTermMeanInvariantUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TowerCT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ratM_ex (D : D7) (W : HSp D) (γ : GA D W) (h : γ ∈ GQ W) :
    ∃ m : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = m.map (incA D) := by
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp h)
  refine ⟨(u : Matrix (Fin W.rank) (Fin W.rank) D.host.E), ?_⟩
  have hu' := congrArg (fun x : GL (Fin W.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E) =>
    (x : Matrix (Fin W.rank) (Fin W.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E))) hu
  exact hu'.symm

variable {D : D7}

def ratM (W : HSp D) (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (ratM_ex D W γ.1 γ.2)

theorem ratM_spec (W : HSp D) (γ : GQ W) : Formalism.L2.Theta.mt W γ.1 = (ratM W γ).map (incA D) := by
  unfold ratM
  exact (ratM_ex D W γ.1 γ.2).choose_spec

theorem map_incA_injective (W : HSp D) :
    Function.Injective fun m : Matrix (Fin W.rank) (Fin W.rank) D.host.E => m.map (incA D) := by
  have : Nontrivial (AF D.host.F) := by
    obtain ⟨v⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h2 : ((0 : AF D.host.F).1 v) = ((1 : AF D.host.F).1 v) := congrArg (fun x : AF D.host.F => x.1 v) h
    exact zero_ne_one h2
  intro a b hab
  ext i j
  have hij : (a.map (incA D)) i j = (b.map (incA D)) i j := by
    rw [show a.map (incA D) = b.map (incA D) from hab]
  simp only [Matrix.map_apply] at hij
  exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective hij

theorem ratM_mul (W : HSp D) (a b : GQ W) : ratM W (a * b) = ratM W a * ratM W b := by
  apply map_incA_injective W
  show (ratM W (a * b)).map (incA D) = (ratM W a * ratM W b).map (incA D)
  rw [Matrix.map_mul, ← ratM_spec, ← ratM_spec, ← ratM_spec]
  exact congrArg Units.val (map_mul (matHom W) a.1 b.1)

theorem ratM_one (W : HSp D) : ratM W (1 : GQ W) = 1 := by
  apply map_incA_injective W
  show (ratM W 1).map (incA D) = (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)
  rw [← ratM_spec, Matrix.map_one _ (map_zero _) (map_one _)]
  exact congrArg Units.val (map_one (matHom W))

private theorem heisO_zero_twisted_operators {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WO V W → ℂ) :
    heisO ψ V W 0 u = u := by
  funext w
  unfold heisO
  simp only [symplOH]
  unfold symplO hO
  simp

def ratAct (W : HSp D) (r : ℕ) : MulAction (GQ W) {y : Matrix (Fin W.rank) (Fin r) D.host.E // y ≠ 0} where
  smul γ y := ⟨ratM W γ * y.1, fun h => y.2 (by
    have := congrArg (ratM W γ⁻¹ * ·) h
    simpa [← Matrix.mul_assoc, ← ratM_mul, ratM_one] using this)⟩
  one_smul y := Subtype.ext (by
    change ratM W 1 * y.1 = y.1
    rw [ratM_one, Matrix.one_mul])
  mul_smul a b y := Subtype.ext (by
    change ratM W (a * b) * y.1 = ratM W a * (ratM W b * y.1)
    rw [ratM_mul, Matrix.mul_assoc])

end GlobalTheory.TowerCT

open GlobalTheory.TowerCT

theorem GlobalTheory.TowerCT.towerConstTermOfCompatible_holds : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTermOfCompatible D := by
  intro D V V' W r C B hS ψ χS χT χS' χT' ω ω' hω hω' hc μ 𝓨 hY ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝 F hFd hFc f hf g
  obtain ⟨hVlc, hVsc, hVt2, hVb, hVtg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hWlc, hWsc, hWt2, hWb, hWtg, -, hWcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hMc : ∀ a b : ℕ, Countable (Matrix (Fin a) (Fin b) D.host.E) := fun a b =>
    inferInstanceAs (Countable (Fin a → Fin b → D.host.E))
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hS
  have hstd : IsStdChar D ψ (-1) := hω.std
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).1
  have hG := GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D

  have hωm : ∀ (p q : GA D V × GA D W) (u : WO V W → ℂ), ω (p * q) u = ω p (ω q u) := by
    intro p q u
    rw [map_mul]
    rfl
  have hL : ∀ (k a : GA D V) (b : GA D W) (u : WO V W → ℂ), ω (k * a, b) u = ω (k, 1) (ω (a, b) u) := by
    intro k a b u
    rw [← hωm, Prod.mk_mul_mk, one_mul]
  have hR : ∀ (a : GA D V) (k b : GA D W) (u : WO V W → ℂ), ω (a, k * b) u = ω (1, k) (ω (a, b) u) := by
    intro a k b u
    rw [← hωm, Prod.mk_mul_mk, one_mul]
  have hLR : ∀ (k a : GA D V) (k' b : GA D W) (u : WO V W → ℂ), ω (k * a, k' * b) u = ω (k, k') (ω (a, b) u) := by
    intro k a k' b u
    rw [← hωm]
    rfl
  have hf₁ : IsThetaFunO ψ V W (ω (g, 1) f) := hω.om_pres _ f hf
  have hfp : ∀ p : GA D V × GA D W, IsThetaFunO ψ V W (ω p f) := fun p => hω.om_pres p f hf
  obtain ⟨hI1, hI2, -, -⟩ := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hS ψ hstd μ 𝓨 hY).1 _ hf₁
  have hvol : κ 𝓝 ≠ ⊤ := vol D V r C hS.frame κ 𝓝 hκ h𝓝
  have : IsFiniteMeasure (κ.restrict 𝓝) := isFiniteMeasure_restrict.mpr hvol

  obtain ⟨tm, htm⟩ : ∃ tm : Matrix (Fin W.rank) (Fin r) D.host.E → (WO V W → ℂ) → ℂ, ∀ y u,
      tm y u = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) u) 0 :=
    ⟨fun y u => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) u) 0, fun _ _ => rfl⟩
  have hsum : ∀ u, IsThetaFunO ψ V W u → HasSum (fun y => tm y u) (u 0) := by
    intro u hu
    simp only [htm]
    exact (GlobalTheory.T.theta_series_summable_on_covolume_domain D V V' W r C C' B hS h1 h2 h3 ψ hstd μ 𝓨 hY u hu).2
  have hrat : ∀ n ∈ NI V C, n ∈ GQ V → ∀ y u, IsThetaFunO ψ V W u → tm y (ω (n, 1) u) = tm y u := by
    intro n hn hnq y u hu
    rw [htm, htm]
    exact GlobalTheory.T.mixedModelTerms_rationalUnipotent_invariant D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY n hn hnq y u hu
  have heqv : ∀ (γ : GA D W) (γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), γ ∈ GQ W →
      Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → ∀ y u, IsThetaFunO ψ V W u → tm (γ₀ * y) (ω (1, γ) u) = tm y u := by
    intro γ γ₀ hγ hγ₀ y u hu
    rw [htm, htm]
    exact GlobalTheory.T.restrictedHeisenbergTerms_permuted_rationalUnitary D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY γ γ₀ hγ hγ₀ y u hu
  have hnon : ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, adj D y * W.gram * y ≠ 0 → ∀ u, IsThetaFunO ψ V W u →
      ∫ n in 𝓝, tm y (ω ((n : GA D V), 1) u) ∂κ = 0 := by
    intro y hy u hu
    simp only [htm]
    exact GlobalTheory.T.anisotropicTerms_mean_zero_unipotentRadical D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY κ 𝓝 hκ h𝓝 y hy u hu
  have hcuspN : ∀ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E),
      IsIsoFrame W L → m.rank = s → ∀ (n' : NI W L) u, IsThetaFunO ψ V W u →
      ∫ n in 𝓝, tm (L * m) (ω ((n : GA D V), (n' : GA D W)) u) ∂κ = ∫ n in 𝓝, tm (L * m) (ω ((n : GA D V), 1) u) ∂κ := by
    intro s L m hL hm n' u hu
    simp only [htm]
    exact GlobalTheory.T.isotropicTermMean_invariant_unipotentRadical D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY κ 𝓝 hκ h𝓝 s L m hL hm n' u hu
  obtain ⟨A, hA⟩ := GlobalTheory.T.mixedModel_thetaSeries_moderate_growth D V V' W r C C' B hS h1 h2 h3 ψ χS χT ω hω μ 𝓨 hY
  obtain ⟨c, hcb⟩ := hA f hf
  have hcont : ∀ y, Continuous fun p : GA D V × GA D W => tm y (ω p f) := by
    intro y
    simp only [htm]
    exact (hcb 1 1).1 y
  have hTm : ∀ y, Measurable (Function.uncurry fun (n : NI V C) (h : GA D W) => tm y (ω ((n : GA D V) * g, h) f)) := by
    intro y
    exact ((hcont y).comp (by fun_prop : Continuous fun q : NI V C × GA D W => ((q.1 : GA D V) * g, q.2))).measurable
  have hKm : ∀ y, Measurable fun h : GA D W => ∫ n in 𝓝, tm y (ω ((n : GA D V) * g, h) f) ∂κ := by
    intro y
    exact (StronglyMeasurable.integral_prod_left (μ := κ.restrict 𝓝) (hTm y).stronglyMeasurable).measurable

  have hb0 := GlobalTheory.T.lintegral_thetaLift_termSum_ne_top D V W r C hS.frame κ 𝓝 hκ h𝓝 ν 𝓕 hν h𝓕 F hFd
    (fun p => ∑' y, ‖tm y (ω p f)‖ₑ)
    (by
      intro n hn hnq a b
      refine tsum_congr fun y => ?_
      show ‖tm y (ω (n * a, b) f)‖ₑ = ‖tm y (ω (a, b) f)‖ₑ
      rw [hL, hrat n hn hnq y _ (hfp _)])
    (by
      intro γ hγ a b
      show ∑' y, ‖tm y (ω (a, γ * b) f)‖ₑ = ∑' y, ‖tm y (ω (a, b) f)‖ₑ
      let γq : GQ W := ⟨γ, hγ⟩
      have hl : ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, ratM W γq⁻¹ * (ratM W γq * y) = y := fun y => by
        rw [← Matrix.mul_assoc, ← ratM_mul, inv_mul_cancel, ratM_one, Matrix.one_mul]
      have hr : ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, ratM W γq * (ratM W γq⁻¹ * y) = y := fun y => by
        rw [← Matrix.mul_assoc, ← ratM_mul, mul_inv_cancel, ratM_one, Matrix.one_mul]
      let e : Matrix (Fin W.rank) (Fin r) D.host.E ≃ Matrix (Fin W.rank) (Fin r) D.host.E :=
        ⟨fun y => ratM W γq * y, fun y => ratM W γq⁻¹ * y, hl, hr⟩
      rw [← e.tsum_eq (fun y => ‖tm y (ω (a, γ * b) f)‖ₑ)]
      refine tsum_congr fun y => ?_
      show ‖tm (ratM W γq * y) (ω (a, γ * b) f)‖ₑ = ‖tm y (ω (a, b) f)‖ₑ
      rw [hR, heqv γ (ratM W γq) hγ (ratM_spec W γq) y _ (hfp _)])
    A c (fun a b => by simp only [htm]; exact (hcb a b).2) g

  obtain ⟨hInt, hSum, hHas⟩ := fub (κ.restrict 𝓝) ν Set.univ 𝓕
    (fun y (n : NI V C) h => tm y (ω ((n : GA D V) * g, h) f)) hTm
    (fun (n : NI V C) h => thetaKO ω ((n : GA D V) * g) h f) F hFd.2.1.measurable
    (fun n h => hsum _ (hfp _)) (by rw [Measure.restrict_univ]; exact hb0)
  simp only [Measure.restrict_univ, integrableOn_univ] at hInt hSum hHas
  set a : Matrix (Fin W.rank) (Fin r) D.host.E → ℂ :=
    fun y => ∫ h in 𝓕, (∫ n in 𝓝, tm y (ω ((n : GA D V) * g, h) f) ∂κ) * F h ∂ν with ha

  have heis0 : ∀ u : WO V W → ℂ, heisO ψ V W 0 u = u := fun u => heisO_zero_twisted_operators ψ V W u
  have hT0 : ∀ (n : NI V C) (h : GA D W),
      tm 0 (ω ((n : GA D V) * g, h) f) = thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) := by
    intro n h
    rw [htm]
    have hiso0 : isoPart V W C' ((0 : Matrix (Fin W.rank) (Fin r) D.host.E).map (incA D)) = 0 := by
      simp [isoPart]
    rw [hiso0, heis0, hL, GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hS ψ χS χT ω hω μ 𝓨 hY n _ (hfp _)]
    have e2 : ((g, h) : GA D V × GA D W) = (1, h) * (g, 1) := by rw [Prod.mk_mul_mk, one_mul, mul_one]
    rw [e2, hωm, hc μ 𝓨 hY h _ hf₁]
    rfl
  have hc0 : ∀ h : GA D W, ∫ _ in 𝓝, thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) ∂κ =
      ((κ 𝓝).toReal : ℂ) * thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) := by
    intro h
    rw [setIntegral_const, Complex.real_smul]
    try rfl
  have ha0 : a 0 = ((κ 𝓝).toReal : ℂ) * Lift.liftInt ν 𝓕 (thetaKO ω') (res V V' W C B μ 𝓨 (ω (g, 1) f)) F 1 := by
    calc a 0 = ∫ h in 𝓕, ((κ 𝓝).toReal : ℂ) * (thetaKO ω' 1 h (res V V' W C B μ 𝓨 (ω (g, 1) f)) * F h) ∂ν := by
          refine integral_congr_ae (ae_of_all _ fun h => ?_)
          simp only [hT0, hc0]
          ring
      _ = _ := by
          rw [integral_const_mul]
          rfl

  have hvanish : ∑' y : {y : Matrix (Fin W.rank) (Fin r) D.host.E // y ≠ 0}, a y.1 = 0 := by
    letI := ratAct W r
    refine GlobalTheory.T.tsum_setIntegral_fundamentalDomain_eq_zero_by_orbits (GA D W) ν (GQ W) {y : Matrix (Fin W.rank) (Fin r) D.host.E // y ≠ 0} 𝓕 h𝓕
      (fun y h => (∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ) * F h)
      (fun y => (hKm y.1).mul hFd.2.1.measurable) ?_ ?_ ?_
    · intro γ y h
      show (∫ n in 𝓝, tm (ratM W γ * y.1) (ω ((n : GA D V) * g, (γ : GA D W) * h) f) ∂κ) * F ((γ : GA D W) * h) =
        (∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ) * F h
      rw [hFd.1 γ γ.2 h]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun n => ?_)
      show tm (ratM W γ * y.1) (ω ((n : GA D V) * g, (γ : GA D W) * h) f) = tm y.1 (ω ((n : GA D V) * g, h) f)
      rw [hR, heqv γ.1 (ratM W γ) γ.2 (ratM_spec W γ) y.1 _ (hfp _)]
    · refine ne_top_of_le_ne_top hSum ?_
      exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        (fun y => ∫⁻ h in 𝓕, ‖(∫ n in 𝓝, tm y (ω ((n : GA D V) * g, h) f) ∂κ) * F h‖ₑ ∂ν)
    · intro y 𝓖 h𝓖 hint
      by_cases hiso : adj D y.1 * W.gram * y.1 = 0
      · obtain ⟨s, L, m, m', hLf, hm, hmm', hy⟩ := rankFac D W r y.1 y.2 hiso
        have hLy : ∀ k : GQ W, ratM W k * y.1 = y.1 → ratM W k * L = L := by
          intro k hk
          rw [hy, ← Matrix.mul_assoc] at hk
          have hk' := congrArg (· * m') hk
          simpa only [Matrix.mul_assoc, hmm', Matrix.mul_one] using hk'
        refine cusp D W s L hLf ν hν F hFd hFc ((MulAction.stabilizer (GQ W) y).map (GQ W).subtype)
          (Subgroup.map_subtype_le _) ?_ ?_ (fun h => ∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ)
          (hKm y.1) ?_ ?_ 𝓖 h𝓖 hint
        · rintro γ ⟨k, hk, rfl⟩ n hn
          have hk1 : ratM W k * y.1 = y.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hk)
          exact (GlobalTheory.T.rationalFrameStabiliser_normalises_unipotentRadical D W s L hLf).1 k.1 k.2 (ratM W k) (ratM_spec W k) (hLy k hk1) n hn
        · intro n hn hnq
          refine ⟨⟨n, hnq⟩, MulAction.mem_stabilizer_iff.mpr (Subtype.ext ?_), rfl⟩
          show ratM W ⟨n, hnq⟩ * y.1 = y.1
          rw [hy, ← Matrix.mul_assoc,
            (GlobalTheory.T.rationalFrameStabiliser_normalises_unipotentRadical D W s L hLf).2 n hn (ratM W ⟨n, hnq⟩) (ratM_spec W ⟨n, hnq⟩)]
        · intro n' hn' h
          have e1 : (fun n : NI V C => tm y.1 (ω ((n : GA D V) * g, n' * h) f)) =
              fun n : NI V C => tm (L * m) (ω ((n : GA D V), n') (ω (g, h) f)) := by
            funext n
            rw [hLR, hy]
          have e2 : (fun n : NI V C => tm y.1 (ω ((n : GA D V) * g, h) f)) =
              fun n : NI V C => tm (L * m) (ω ((n : GA D V), 1) (ω (g, h) f)) := by
            funext n
            rw [hL, hy]
          show ∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, n' * h) f) ∂κ = ∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ
          rw [e1, e2]
          exact hcuspN s L m hLf hm ⟨n', hn'⟩ _ (hfp _)
        · rintro γ ⟨k, hk, rfl⟩ h
          have hk1 : ratM W k * y.1 = y.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hk)
          refine integral_congr_ae (ae_of_all _ fun n => ?_)
          show tm y.1 (ω ((n : GA D V) * g, (k : GA D W) * h) f) = tm y.1 (ω ((n : GA D V) * g, h) f)
          conv_lhs => rw [← hk1]
          rw [hR, heqv k.1 (ratM W k) k.2 (ratM_spec W k) y.1 _ (hfp _)]
      · have hz : ∀ h, ∫ n in 𝓝, tm y.1 (ω ((n : GA D V) * g, h) f) ∂κ = 0 := by
          intro h
          have e2 : (fun n : NI V C => tm y.1 (ω ((n : GA D V) * g, h) f)) =
              fun n : NI V C => tm y.1 (ω ((n : GA D V), 1) (ω (g, h) f)) := by
            funext n
            rw [hL]
          rw [e2]
          exact hnon y.1 hiso _ (hfp _)
        simp [hz]
  have hbsum : HasSum (Set.indicator {y | y ≠ 0} a) 0 := by
    have hs := hHas.summable.indicator {y | y ≠ 0}
    have ht : ∑' y, Set.indicator {y | y ≠ 0} a y = 0 := by
      rw [← tsum_subtype]
      exact hvanish
    rw [← ht]
    exact hs.hasSum
  have hfull : HasSum a (a 0 + 0) := by
    classical
    have h0 := (hasSum_ite_eq (0 : Matrix (Fin W.rank) (Fin r) D.host.E) (a 0)).add hbsum
    convert h0 using 1
    funext y
    by_cases hy0 : y = 0
    · subst hy0
      simp
    · simp [hy0]
  refine ⟨hvol, hI1, hI2,
    fun g₁ => GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hFd g₁,
    GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec hG hθ hω' hI2 hν h𝓕 hFd 1, hInt, ?_⟩
  exact (hHas.unique hfull).trans ((add_zero _).trans ha0)

end
