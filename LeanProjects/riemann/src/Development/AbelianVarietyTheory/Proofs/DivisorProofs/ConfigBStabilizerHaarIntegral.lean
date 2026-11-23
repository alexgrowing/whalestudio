import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralConvergesStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeFubini

theorem theta_cone_eq : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h h₁,
        G₁.M'.I om₁' (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ')) h₁ =
          ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) h₁ * (X.ν l : ℂ) *
            ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁
  have l1 := GlobalTheory.T.config_b_stabilizer_integral_unfold hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁
  have l2 := GlobalTheory.T.config_b_stabilizer_integral_finite hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁
  have l3 := GlobalTheory.T.config_b_stabilizer_integral_converges hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁
  have key : ∀ g, theta om₁' (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ')) g h₁ =
      ∫ k, ∫ l, theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) g h₁ * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) ∂μ ∂μK := by
    intro g
    rw [← l2 g]
    unfold theta
    congr 1
    exact funext (l1 g)
  unfold Model.I
  simp_rw [key]
  exact l3

end GlobalTheory.ConeFubini
