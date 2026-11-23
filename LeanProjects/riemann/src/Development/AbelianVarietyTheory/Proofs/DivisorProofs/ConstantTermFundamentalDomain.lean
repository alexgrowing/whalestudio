import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneIntegralSkewHermitianTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneAutomorphicFunctionTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneTwistConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFunctionRadialLogDependenceStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section

namespace GlobalTheory.ThKCtFin

theorem ctFin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → (∀ Φ ∈ PolData B G.M, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, ∃ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ ∧ ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m → ∫ u in 𝓕, G.M.I om Φ (u.1 * (m * h)) ∂μ = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ)) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, ∃ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (c : Fin N → Fin (K + 1) → ℂ), Function.Injective χ ∧ ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m → ∫ u in 𝓕, G.M'.I om' Φ' (u.1 * (m * h)) ∂μ = ∑ i, ∑ k, c i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA
  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hcm
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have key : ∀ f : UA σ G.W.J → ℂ, (∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧
      IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x))) →
      ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J,
      ∃ (N K : ℕ) (χ : Fin N → (AE F E)ˣ →* ℂˣ) (cc : Fin N → Fin (K + 1) → ℂ), Function.Injective χ ∧
        ∀ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' t 1 m →
          ∫ u in 𝓕, f (u.1 * (m * h)) ∂μ =
            ∑ i, ∑ k, cc i k * ((χ i t : ℂˣ) : ℂ) * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) ^ (k : ℕ) := by
    intro f hf μ 𝓕 h1 h2 h3 h
    have hc1 := GlobalTheory.T.adapted_plane_integral_skew_hermitian_twist hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA hσ c hc hcs f hf μ 𝓕 h1 h2 h3 h
    have hl := GlobalTheory.T.adapted_plane_automorphic_function_twist hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA hσ c hc hcs f hf μ 𝓕 h1 h2 h3 h
    have hfd := GlobalTheory.T.adapted_plane_twist_constant_term hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA hσ c hc hcs f hf μ 𝓕 h1 h2 h3 h
    obtain ⟨N, K, χ, cc, hinj, he⟩ := GlobalTheory.T.invariant_function_radial_log_dependence F E (GlobalTheory.T.continuous_log_hom_is_multiple_of_log_abs F E) _ hc1 hl hfd
    refine ⟨N, K, χ, cc, hinj, fun t m hm => ?_⟩
    have e : leviElt σ G.W W₁ H' t = m :=
      GlobalTheory.T.levi_element_unique F E σ B _ _ _ G.W hT.geo.hW d₁ W₁ H' i₀ i₁ hA t _ _ (isLevi_leviElt ⟨m, hm⟩) hm
    rw [← he t, ctLevi_apply, e]
  exact ⟨fun Φ hΦ => key _ (GlobalTheory.T.exists_maximal_compact_invariant F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ),
    fun Φ' hΦ' => key _ (GlobalTheory.T.exists_maximal_compact_invariant_dual F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ' hΦ')⟩

end GlobalTheory.ThKCtFin
