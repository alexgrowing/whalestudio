import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFiniteApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapIntertwinesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IsoXDecay

theorem thetaSum_decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ φ ∈ schA F (Fin n × Fin d₁), ∀ N K : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := by
  intro hKP F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev hB hsig φ hφ N K hN
  obtain ⟨S, hSf, hSs, hS⟩ := GlobalTheory.T.schwartz_finite_approximation F E σ B n d₁ X W₁ M₁ H.y hB hM₁ φ hφ N hN
  have hC : ∀ Φ, Φ ∈ S → ∃ C : ℝ, ∀ w : Fin d₁ → E, (∀ i, ∃ o : 𝓞 E, (N : E) * w i = o) →
      ‖thetaSum F (e' (M₁.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F H.y) (incV F w)) Φ))‖ *
        (1 + ∑ i, ∑ v : InfinitePlace E, v (w i)) ^ K ≤ C := fun Φ hΦ =>
    GlobalTheory.T.evaluation_map_intertwines hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev hB hsig Φ (hSs hΦ) N K hN
  choose! C hC using hC
  refine ⟨∑ Φ ∈ hSf.toFinset, max (C Φ) 0, fun w hw => ?_⟩
  obtain ⟨Φ, hΦS, hΦe⟩ := hS w hw
  rw [hΦe]
  calc _ ≤ C Φ := hC Φ hΦS w hw
    _ ≤ max (C Φ) 0 := le_max_left _ _
    _ ≤ _ := Finset.single_le_sum (f := fun Φ => max (C Φ) 0) (fun _ _ => le_max_right _ _) (hSf.mem_toFinset.2 hΦS)

end GlobalTheory.IsoXDecay
