import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCocompactInArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesRationalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeromorphicIdentityContinuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableMeromorphicContinuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesMeasurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinMeromorphicContinuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicParamIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeSmallMero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem topUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact ⟨inferInstance, inferInstanceAs (SecondCountableTopology (UG (cA σ) (incM F J)))⟩

theorem continuous_ht (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous fun g : UA σ J => (ht g : ℝ) := by
  have h1 : Continuous fun g : UA σ J => heightGL F g.1 := (GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val
  exact NNReal.continuous_coe.comp h1

theorem ct_mero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om', IsTriple B G X om om' → ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Eis : ℂ → UA σ G.V'.J → ℂ, GlobalTheory.ConeSmall.IsEisSer K H.x Eis →
    GlobalTheory.ConeSmallCT.EisGood b Eis → ∀ (μ₁ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ₁.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ₁ → μ₁ 𝓕 = 1 → ∀ h,
      (∀ s₀ : ℂ, MeromorphicAt (fun s => ∫ u in 𝓕, GlobalTheory.ConeSmallCT.Bint G.M' om' Φ' Eis s (u.1 * h) ∂μ₁) s₀) ∧
      AnalyticAt ℂ (fun s => ∫ u in 𝓕, GlobalTheory.ConeSmallCT.Bint G.M' om' Φ' Eis s (u.1 * h) ∂μ₁) (-((((b + 2 : ℕ) : ℂ) - 1) / 2)) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' hT K hK Φ' hΦ' Eis hES hEG μ₁ 𝓕 hμ₁ h𝓕 h1 h

  have hV' : IsPair B G.M' X.α (X.α / X.β) om' G.q (b + 2 - G.q) (a + (b + 2) - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
      resW := by rw [add_comm a (b + 2)]; exact GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resα hT.chars.resβ,
      weil := hT.weil' }
  have hΦs : Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    GlobalTheory.ThKRatInv.polData_le_schA B G.M' hT.geo.hM' (Submodule.mem_inf.1 hΦ').1
  obtain ⟨hcont, hinv, -⟩ := (GlobalTheory.T.theta_basic_properties hKP.base F E σ B (b + 2) (a + (b + 2)) G.V' G.W G.M' X.α (X.α / X.β) om'
    _ _ _ _ hV').1 Φ' hΦs
  have hdec := GlobalTheory.T.schwartz_orbit_decay hKP F E σ B (b + 2) (a + (b + 2)) G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hV' Φ'
    (Submodule.mem_inf.1 hΦ').2
  obtain ⟨Kc, hKc, hKcov⟩ := GlobalTheory.UnipCocompact.cocompact_unip F E σ B a (b + 2) G X om om' hT (a + b) G₁.W H' a
    (a + b + 1) hC.hH'
  obtain ⟨hTGV, hSCV⟩ := topUA σ G.V'.J
  obtain ⟨hTGW, hSCW⟩ := topUA σ G.W.J
  haveI := hTGV; haveI := hSCV; haveI := hTGW; haveI := hSCW
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have hfin : G.M'.μ G.M'.dom < ⊤ :=
    GlobalTheory.UnitaryVol.measure_dom_lt_top F E σ B a (b + 2) G X om om' hKP.siegelSetUnitary hT
  haveI : IsFiniteMeasure (μ₁.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := isFiniteMeasure_restrict.2 hfin.ne

  have hθ : ∀ N : ℕ, ∃ M : ℝ, ∀ g (u : unip σ G.W H'), ‖theta om' Φ' g (u.1 * h)‖ * (qht g : ℝ) ^ N ≤ M := by
    intro N
    obtain ⟨C, k, hCk⟩ := hdec N
    have hc : Continuous fun u : unip σ G.W H' => (ht (u.1 * h) : ℝ) :=
      (continuous_ht σ G.W.J).comp (continuous_subtype_val.mul continuous_const)
    obtain ⟨Cw, hCw⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0 * Cw ^ k, fun g u => ?_⟩
    obtain ⟨γ, hγ, hγu⟩ := hKcov u
    have e1 := hinv 1 (one_mem _) γ.1 (Subgroup.mem_subgroupOf.1 hγ) g (u.1 * h)
    rw [one_mul] at e1
    rw [← e1]
    refine (hCk g _).trans ?_
    have hb := hCw _ hγu
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] at hb
    have hb' : (ht (γ.1 * (u.1 * h)) : ℝ) ≤ Cw := by simpa [mul_assoc] using hb
    calc C * (ht (γ.1 * (u.1 * h)) : ℝ) ^ k ≤ max C 0 * (ht (γ.1 * (u.1 * h)) : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * Cw ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb' k) (le_max_right _ _)

  have KC : ∀ (s₀ : ℂ) (r : ℝ) (Hol : ℂ → UA σ G.V'.J → ℂ) (C : ℝ) (N : ℕ),
      (∀ g, DifferentiableOn ℂ (Hol · g) (Metric.ball s₀ r)) →
      (∀ s ∈ Metric.ball s₀ r, ∀ g, ‖Hol s g‖ ≤ C * (qht g : ℝ) ^ N) →
      (∀ s ∈ Metric.ball s₀ r, Measurable (Hol s)) →
      DifferentiableOn ℂ (fun s => ∫ u in 𝓕, ∫ g in G.M'.dom, theta om' Φ' g (u.1 * h) * Hol s g ∂G.M'.μ ∂μ₁)
        (Metric.ball s₀ r) := by
    intro s₀ r Hol C N hd hb hm
    obtain ⟨M, hM⟩ := hθ N
    refine GlobalTheory.T.holomorphic_param_integral (G.M'.μ.restrict G.M'.dom) (μ₁.restrict 𝓕) (fun u g => theta om' Φ' g (u.1 * h)) Hol s₀ r
      (max C 0 * M) ?_ hd ?_
    · intro s hs
      have hc : Continuous fun p : unip σ G.W H' × UA σ G.V'.J => theta om' Φ' p.2 (p.1.1 * h) :=
        hcont.comp (continuous_snd.prodMk ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
      exact hc.aestronglyMeasurable.mul ((hm s hs).comp measurable_snd).aestronglyMeasurable
    · intro s hs u g
      rw [norm_mul]
      calc ‖theta om' Φ' g (u.1 * h)‖ * ‖Hol s g‖
          ≤ ‖theta om' Φ' g (u.1 * h)‖ * (max C 0 * (qht g : ℝ) ^ N) :=
            mul_le_mul_of_nonneg_left ((hb s hs g).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (norm_nonneg _)
        _ = max C 0 * (‖theta om' Φ' g (u.1 * h)‖ * (qht g : ℝ) ^ N) := by ring
        _ ≤ max C 0 * M := mul_le_mul_of_nonneg_left (hM g u) (le_max_right _ _)

  have hloc1 : ∀ g, ∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (Hl : ℂ → ℂ), U ∈ 𝓝 s₀ ∧
      (∀ s ∈ U, s ≠ s₀ → Hl s = (s - s₀) ^ k * Eis s g) ∧ DifferentiableOn ℂ Hl U := by
    intro g s₀
    obtain ⟨k, U, Hl, C, N, hU, heq, hd, -⟩ := hEG.1 s₀
    exact ⟨k, U, fun s => Hl s g, hU, fun s hs hne => heq s hs hne g, hd g⟩
  have hinvE : ∀ s₀ : ℂ, ∀ γ ∈ ratU σ G.V'.J, ∀ g, ∀ᶠ s in 𝓝[≠] s₀, Eis s (γ * g) = Eis s g :=
    fun s₀ γ hγ g => GlobalTheory.T.meromorphic_identity_continuation (fun s => Eis s (γ * g)) (fun s => Eis s g) ((((b + 2 : ℕ) : ℝ) - 1) / 2)
      (hloc1 (γ * g)) (hloc1 g) (fun s hs => GlobalTheory.T.eisenstein_series_rational_invariant K H.x Eis hES s hs γ hγ g) s₀
  have hmE : ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, Measurable (Eis s) :=
    GlobalTheory.T.measurable_meromorphic_continuation Eis ((((b + 2 : ℕ) : ℝ) - 1) / 2)
      (fun s₀ => by
        obtain ⟨k, U, Hl, C, N, hU, heq, hd, -⟩ := hEG.1 s₀
        exact ⟨k, U, Hl, hU, heq, hd⟩)
      (GlobalTheory.T.eisenstein_series_measurable hKP B G.V' G.q (b + 2 - G.q) hT.base hT.geo.hV' K hK H.x Eis hES)
  obtain ⟨hlocal, r₀, C₀, N₀, hr₀, hd₀, hb₀, hm₀⟩ := GlobalTheory.T.eisenstein_meromorphic_continuation b Eis hEG hinvE hmE
  refine ⟨fun s₀ => ?_, ?_⟩
  · obtain ⟨k, r, Hol, C, N, hr, heq, hd, hb, hm⟩ := hlocal s₀
    have hD := KC s₀ r Hol C N hd hb hm
    refine ⟨k + 1, ?_⟩
    have han : AnalyticAt ℂ (fun z => (z - s₀) *
        ∫ u in 𝓕, ∫ g in G.M'.dom, theta om' Φ' g (u.1 * h) * Hol z g ∂G.M'.μ ∂μ₁) s₀ :=
      (analyticAt_id.sub analyticAt_const).mul (hD.analyticAt (Metric.ball_mem_nhds s₀ hr))
    refine han.congr ?_
    filter_upwards [Metric.ball_mem_nhds s₀ hr] with z hz
    by_cases hzs : z = s₀
    · subst hzs; simp
    · have e : ∀ u : unip σ G.W H', ∫ g in G.M'.dom, theta om' Φ' g (u.1 * h) * Hol z g ∂G.M'.μ =
          (z - s₀) ^ k * GlobalTheory.ConeSmallCT.Bint G.M' om' Φ' Eis z (u.1 * h) := by
        intro u
        rw [GlobalTheory.ConeSmallCT.Bint, ← integral_const_mul]
        congr 1
        funext g
        rw [heq z hz hzs g]
        ring
      simp only [e, integral_const_mul, smul_eq_mul]
      ring
  · exact (KC _ r₀ Eis C₀ N₀ hd₀ hb₀ hm₀).analyticAt (Metric.ball_mem_nhds _ hr₀)

end GlobalTheory.ConeSmallMero
