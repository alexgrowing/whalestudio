import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEigenFactor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_triple_eigen_factor : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    (∃ Φ₁' ∈ PolData B G₁.M' ⊓ G₁.M'.So B.ψ B.τ₁, G₁.M'.I om₁' Φ₁' ≠ 0) →
    ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ (h : UA σ G.W.J) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi (W₁ := G₁.W) H' 1 h₁ m ∧
      G₁.M'.I om₁' (cone B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (om' (1, h) Φ')) h₁ ≠ 0 := by
  first | exact @GlobalTheory.ConeBNZ.nonzero | exact GlobalTheory.ConeBNZ.nonzero | (intros; apply GlobalTheory.ConeBNZ.nonzero <;> assumption)
