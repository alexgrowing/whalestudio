import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

namespace GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre

section Abstract

variable {X G : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]

theorem exists_fibreIntegral (F : X × ℝ → ℂ) (hF : Continuous F) (hs : HasCompactSupport F) (r : ℂ) :
    ∃ f₁ : CompactlySupportedContinuousMap X ℂ, ∀ x, f₁ x = r * ∫ t, F (x, t) := by
  have hK : IsCompact (Prod.snd '' tsupport F) := hs.isCompact.image continuous_snd
  have hK₁ : IsCompact (Prod.fst '' tsupport F) := hs.isCompact.image continuous_fst
  have hcont : Continuous fun x : X => ∫ t, F (x, t) := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support (f := fun x t => F (x, t)) hK ?_ ?_
    · exact hF.continuousOn
    · intro p x _ hx
      by_contra h
      exact hx ⟨(p, x), subset_tsupport _ h, rfl⟩
  refine ⟨⟨⟨fun x => r * ∫ t, F (x, t), continuous_const.mul hcont⟩, ?_⟩, fun x => rfl⟩
  refine HasCompactSupport.intro hK₁ fun x hx => ?_
  have h0 : ∀ t, F (x, t) = 0 := by
    intro t
    by_contra h
    exact hx ⟨(x, t), subset_tsupport _ h, rfl⟩
  simp [h0]

theorem integral_eq_of_map (e : X × ℝ ≃ₜ G) (ν : Measure X) [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    (μ : Measure G) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map e (ν.prod volume) = c • μ) (f : G → ℂ) (hf : Continuous f) (hs : HasCompactSupport f)
    (f₁ : CompactlySupportedContinuousMap X ℂ)
    (hf₁ : ∀ x, f₁ x = (c.toReal : ℂ)⁻¹ * ∫ t, f (e (x, t)))
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : G → K) (w : X → K)
    (hW : Continuous W) (hw : ∀ x t, W (e (x, t)) = w x) :
    ∫ g, f g • W g ∂μ = ∫ x, f₁ x • w x ∂ν := by
  have hr : c.toReal ≠ 0 := (ENNReal.toReal_pos hc0 hct).ne'
  have hrC : (c.toReal : ℂ) ≠ 0 := by exact_mod_cast hr
  have hFc : Continuous fun p : X × ℝ => f (e p) := hf.comp e.continuous
  have hFs : HasCompactSupport fun p : X × ℝ => f (e p) := hs.comp_homeomorph e
  have hint : Integrable (fun p : X × ℝ => f (e p) • W (e p)) (ν.prod volume) :=
    (hFc.smul (hW.comp e.continuous)).integrable_of_hasCompactSupport hFs.smul_right
  have h1 : c.toReal • ∫ g, f g • W g ∂μ = ∫ p, f (e p) • W (e p) ∂(ν.prod volume) := by
    rw [← integral_smul_measure, ← hmap]
    exact e.measurableEmbedding.integral_map _
  have h2 : ∫ p, f (e p) • W (e p) ∂(ν.prod volume) = ∫ x, (∫ t, f (e (x, t))) • w x ∂ν := by
    rw [integral_prod _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hw]
    exact integral_smul_const _ _
  have h3 : ∫ x, f₁ x • w x ∂ν = (c.toReal : ℂ)⁻¹ • ∫ x, (∫ t, f (e (x, t))) • w x ∂ν := by
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf₁, mul_smul]
  rw [h3, ← h2, ← h1, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ hrC, one_smul]

end Abstract

theorem exists_normOne_integral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL E a)) [ν.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ → Measure.map (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (normOneGL E a) ℂ, ∀ (K : Type) [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : GA E a → K), Continuous W → (∀ t g, W (splitCentre E a t * g) = W g) → ∫ g, f g • W g ∂μ = ∫ x, f₁ x • W (x : GA E a) ∂ν := by
  intro E _ _ _ a ha μ _ ν _ c hc0 hct hmap f hf hs
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have hfun : (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e := by
    funext p
    exact (he p.1 p.2).symm
  rw [hfun] at hmap
  obtain ⟨f₁, hf₁⟩ := exists_fibreIntegral (fun p : normOneGL E a × ℝ => f (e p))
    (hf.comp e.continuous) (hs.comp_homeomorph e) ((c.toReal : ℂ)⁻¹)
  refine ⟨f₁, fun K _ _ _ W hW hinv => ?_⟩
  exact integral_eq_of_map e ν μ c hc0 hct hmap f hf hs f₁ hf₁ W (fun x => W (x : GA E a)) hW
    (fun x t => by rw [he, hinv])

end GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre
