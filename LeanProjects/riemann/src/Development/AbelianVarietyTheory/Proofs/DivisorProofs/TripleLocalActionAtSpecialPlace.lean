import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalThetaFactorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SoLocW

open scoped Matrix

theorem soLoc_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ → φ₁ ∈ G.M'.SoLoc B.ψ B.τ₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT h hh φ hφ φ₁ hφ₁ hA
  obtain ⟨hφSB, ι, hι, hsupp⟩ := hφ
  refine ⟨hφ₁, ι, hι, fun Y hY => ?_⟩
  have h1 : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F B.v₁) := by
    intro u _
    simp [mat]
  obtain ⟨c, P, Q, hPQ⟩ := GlobalTheory.T.linear_bar_local_theta_factor hK.base F E σ B a a' G X om om' hT B.v₁ B.τ₁ ι hι 1 h1 h hh φ hφSB φ₁ hφ₁ hA
  have hr : (P.1 * Y * Q.1).rank = Y.rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit)]
  rw [hPQ, hsupp _ (by rw [hr]; exact hY), mul_zero]

end GlobalTheory.SoLocW
