import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlanePairInduction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_plane_pair_induction : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∀ g : UA σ X.J, ∀ K : Set (UA σ X.J), IsCompact K → K ⊆ unip σ X H →
      ∀ N₀ K' : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ u ∈ K, ∀ h : UA σ W.J, ∀ N : ℕ, 1 ≤ N → ∀ w : Fin d → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
        ∀ ξ : Fin d₂ × Fin d → F,
          ‖e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (om (u, 1) (om (g, h) Φ))) (fun i => algebraMap F (AF F) (ξ i))‖ *
            (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ * (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K' ≤ C * ((N : ℝ) * ht h) ^ k := by
  first | exact @GlobalTheory.MixedPtDecay.main | exact GlobalTheory.MixedPtDecay.main | (intros; apply GlobalTheory.MixedPtDecay.main <;> assumption)
