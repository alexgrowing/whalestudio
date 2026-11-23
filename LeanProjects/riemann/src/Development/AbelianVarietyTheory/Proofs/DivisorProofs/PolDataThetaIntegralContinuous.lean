import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralsContinuousAutomorphicStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK

theorem thetaIntegral_continuous : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    (∀ Φ ∈ PolData B G.M, Continuous (G.M.I om Φ)) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Continuous (G.M'.I om' Φ') := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT
  have h := GlobalTheory.T.theta_integrals_continuous_automorphic hK F E σ B a a' G X om om' hT
  exact ⟨fun Φ hΦ => (h.1 Φ hΦ).1, fun Φ' hΦ' => (h.2 Φ' hΦ').1⟩

end GlobalTheory.ThK
