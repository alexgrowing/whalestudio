import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationLocalIntertwiner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleSmallerGeometryConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleRestrictionHermitianAdaptedPlaneStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.ConeModulus

theorem integral_eq_of_lintegral_comp {X : Type} [MeasurableSpace X] (ν : Measure X) (f f' : X → ℂ) (c : ℝ) (hc : 0 < c)
    (hf : AEMeasurable f ν) (hf' : AEMeasurable f' ν)
    (h : ∀ ψ : ℂ → ENNReal, Measurable ψ → ENNReal.ofReal c * ∫⁻ x, ψ (f' x) ∂ν = ∫⁻ x, ψ (f x) ∂ν) :
    (c : ℂ) * ∫ x, f' x ∂ν = ∫ x, f x ∂ν := by
  have hmap : ν.map f = ENNReal.ofReal c • ν.map f' := by
    ext s hs
    have hψ : Measurable (s.indicator (1 : ℂ → ENNReal)) := measurable_one.indicator hs
    have h1 := h _ hψ
    rw [← lintegral_map' hψ.aemeasurable hf', ← lintegral_map' hψ.aemeasurable hf,
      lintegral_indicator_one hs, lintegral_indicator_one hs] at h1
    rw [Measure.smul_apply, smul_eq_mul, h1]
  have e1 : ∫ x, f x ∂ν = ∫ z, z ∂(ν.map f) := (integral_map hf aestronglyMeasurable_id).symm
  have e2 : ∫ x, f' x ∂ν = ∫ z, z ∂(ν.map f') := (integral_map hf' aestronglyMeasurable_id).symm
  rw [e1, e2, hmap, integral_smul_measure, ENNReal.toReal_ofReal hc.le, Complex.real_smul]

theorem integral_translate_levi : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ (t : (AE F E)ˣ) (m₀ : UA σ G.V.J), IsLevi (W₁ := X₁) H₀ (Units.map (cA σ : AE F E →* AE F E) t) 1 m₀ → ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x}) 𝓓 G.M.μ → ∀ Φ ∈ PolData B G.M, ∀ h, (((absE F E t : ℝ) ^ ((a : ℝ) - 1) : ℝ) : ℂ) * ∫ g in 𝓓, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (m₀⁻¹ * g, h) Φ))) ∂G.M.μ = ∫ g in 𝓓, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ))) ∂G.M.μ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev t m₀ hm₀
    𝓓 h𝓓 Φ hΦ h
  classical
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := hT.geo.hM.haar
  set f : UA σ G.V.J → ℂ := fun g => thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ))) with hf
  have hQ : ∀ q, q ∈ ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x} ↔ q ∈ ratU σ G.V.J ∧ mat q *ᵥ incV F H₀.x = incV F H₀.x := fun q =>
    ⟨fun hq => ⟨hq.1, StabInv.fix_of_mem_closure _ hq.2⟩, fun hq => ⟨hq.1, Subgroup.subset_closure hq.2⟩⟩
  have hqinv : ∀ q ∈ ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x}, ∀ g, f (q * g) = f g := fun q hq g =>
    ConeUnfold.coneTerm_left_inv_val hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂
      hH₀ hM₂ hev Φ hΦ h _ hQ q hq g
  have hninv : ∀ n ∈ unip σ G.V H₀, ∀ g, f (n * g) = f g := fun n hn g =>
    GlobalTheory.T.triple_smaller_geometry_constant_term hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h n hn g
  have hmeas : AEStronglyMeasurable f G.M.μ := GlobalTheory.T.second_configuration_triple_compatible hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁
    X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h
  have hmeas' : AEStronglyMeasurable (fun g => f (m₀⁻¹ * g)) G.M.μ :=
    hmeas.comp_measurePreserving (measurePreserving_mul_left G.M.μ m₀⁻¹)
  have hc : 0 < (absE F E t : ℝ) ^ ((a : ℝ) - 1) := Real.rpow_pos_of_pos (GlobalTheory.CtTyp.absE_pos t) _
  exact integral_eq_of_lintegral_comp (G.M.μ.restrict 𝓓) f (fun g => f (m₀⁻¹ * g)) _ hc hmeas.aemeasurable.restrict
    hmeas'.aemeasurable.restrict fun ψ hψ =>
      GlobalTheory.T.triple_restriction_hermitian_adapted_plane F E σ B a b G X om om' hT V₂ n₁ X₁ H₀ j₀ j₁ (a + b) G₁.W M₂ hV₂ hH₀ hM₂ t m₀ hm₀ 𝓓 h𝓓
        (fun g => ψ (f g)) (hψ.comp_aemeasurable hmeas.aemeasurable)
        (fun q hq g => by simp only [hqinv q hq g]) (fun n hn g => by simp only [hninv n hn g])

end GlobalTheory.ThK.ConeModulus

end
