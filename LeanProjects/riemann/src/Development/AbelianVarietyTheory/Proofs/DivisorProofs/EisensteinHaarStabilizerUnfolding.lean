import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicParameterIntegralStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallHol

theorem coneI_differentiableOn : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, DifferentiableOn ℂ (fun z => GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z h) {z : ℂ | 1 < z.re} := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h

  obtain ⟨K₀, μK₀, μ₀, hK₀, hK₀c, -, -⟩ :=
    GlobalTheory.T.theta_stabilizer_exists hK.base F E σ B (b + 2) G.V' G.q (b + 2 - G.q) hT.base hT.geo.hV'
  have hKK : K = K₀ := by
    ext g; rw [hKs g, hK₀ g]
  subst hKK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK₀c
  haveI : IsFiniteMeasure μK := inferInstance

  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eq⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := eq.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := eq.secondCountableTopology
  haveI : T2Space (AE F E) := eq.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ

  have hν : Continuous fun l : (AE F E)ˣ => ((X.ν l : Circle) : ℂ) := by
    have h1 : Continuous fun l : (AE F E)ˣ => X.α l / X.β l :=
      hT.chars.heckeα.1.div' hT.chars.heckeβ.1
    have h2 : Continuous (X.α / X.β) := h1.congr fun l => (MonoidHom.div_apply _ _ _).symm
    exact continuous_subtype_val.comp h2
  have ha : Continuous fun l : (AE F E)ˣ => (absE F E l : ℝ) :=
    NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE
  have hpos : ∀ l : (AE F E)ˣ, 0 < (absE F E l : ℝ) := fun l => by
    have h0 := congrArg (fun t : ℝ≥0 => (t : ℝ)) (map_mul_eq_one (absE F E) (mul_inv_cancel l))
    simp only [NNReal.coe_mul, NNReal.coe_one] at h0
    rcases (NNReal.coe_nonneg (absE F E l)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at h0; exact absurd h0 zero_ne_one
  obtain ⟨g, hg, hgb⟩ := GlobalTheory.T.config_b_stabilizer_integral_identity hK F E σ B a b G G₁ H H' hC e' he' K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  have hm := GlobalTheory.T.config_b_stabilizer_integral_bound hK F E σ B a b G G₁ H H' hC e' he' K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  have hA : AEStronglyMeasurable (Function.uncurry fun (k : K) (l : (AE F E)ˣ) =>
      G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 * ((X.ν l : Circle) : ℂ)) (μK.prod μ) :=
    hm.mul ((hν.measurable.comp measurable_snd).aestronglyMeasurable)
  have key := GlobalTheory.T.holomorphic_parameter_integral μK μ (fun (k : K) (l : (AE F E)ˣ) =>
      G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 * ((X.ν l : Circle) : ℂ))
    (fun l => (absE F E l : ℝ)) ha.measurable hpos hA g hg (fun k l => by
      rw [norm_mul, Circle.norm_coe, mul_one]; exact hgb k l)
  exact key

end GlobalTheory.ConeSmallHol

end
