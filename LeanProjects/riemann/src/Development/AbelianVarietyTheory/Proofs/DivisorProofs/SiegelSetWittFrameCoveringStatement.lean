import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameCovering
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_witt_frame_covering : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ (hσ : ∀ x, σ (σ x) = x) (e : E) (he : e ≠ 0) (Cf : Set (GFin σ (e • W.J.map σ))), IsCompact Cf →
      ∀ L : ℕ, ∃ N : ℕ, ∀ Φ ∈ schA F (Fin n × Fin d), Φ ∈ M.So B.ψ B.τ₁ → ∃ C : ℝ,
        ∀ (h : UA σ W.J) (g : UA σ X.J), projFin σ (e • W.J.map σ) (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J he h) ∈ Cf →
        ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ k ∈ K, g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om Φ g h‖ * (1 + ∏ i, t i) ^ L ≤ C * (ht h : ℝ) ^ N := by
  first | exact @GlobalTheory.ThetaSoSiegel.theta_decay_height_pow | exact GlobalTheory.ThetaSoSiegel.theta_decay_height_pow | (intros; apply GlobalTheory.ThetaSoSiegel.theta_decay_height_pow <;> assumption)
