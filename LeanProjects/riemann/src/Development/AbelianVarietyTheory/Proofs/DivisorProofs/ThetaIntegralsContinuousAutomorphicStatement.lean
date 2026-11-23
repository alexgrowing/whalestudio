import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralsContinuousAutomorphic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integrals_continuous_automorphic : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → (∀ Φ ∈ PolData B G.M, Continuous (G.M.I om Φ) ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M.I om Φ (γ * h) = G.M.I om Φ h) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Continuous (G.M'.I om' Φ') ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  first | exact @GlobalTheory.ThKCont.thCont | exact GlobalTheory.ThKCont.thCont | (intros; apply GlobalTheory.ThKCont.thCont <;> assumption)
