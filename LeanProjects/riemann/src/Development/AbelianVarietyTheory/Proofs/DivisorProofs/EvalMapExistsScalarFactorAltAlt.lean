import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSchwartzSetIntegralShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAdaptedPlaneEigenMapStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.XiTermDecay

theorem decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ N K : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ ξ : Fin n → E, (∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) →
      ‖thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Ψ))‖ *
        (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤ C := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hAd hM₁ e₀ hEv hB hM hXW Ψ hΨ N K hN
  obtain ⟨S, hSfin, hSsch, hS⟩ := GlobalTheory.T.finite_schwartz_set_integral_shift F E σ B n d X W M H'.y hB hM Ψ hΨ N hN
  have hC : ∀ Φ ∈ S, ∃ C : ℝ, ∀ ξ : Fin n → E,
      ‖thetaSum F (e₀ (M.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F ξ) (incV F H'.y)) Φ))‖ *
        (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤ C :=
    fun Φ hΦ => GlobalTheory.T.models_adapted_plane_eigen_map hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hAd hM₁ e₀ hEv hB hM hXW Φ (hSsch hΦ) K
  choose! C hC using hC
  classical
  refine ⟨∑ Φ ∈ hSfin.toFinset, max (C Φ) 0, fun ξ hξ => ?_⟩
  obtain ⟨Φ, hΦ, hEq⟩ := hS ξ hξ
  rw [hEq]
  refine (hC Φ hΦ ξ).trans ((le_max_left _ 0).trans ?_)
  exact Finset.single_le_sum (f := fun Φ => max (C Φ) 0) (fun _ _ => le_max_right _ _) (hSfin.mem_toFinset.2 hΦ)

end GlobalTheory.XiTermDecay
