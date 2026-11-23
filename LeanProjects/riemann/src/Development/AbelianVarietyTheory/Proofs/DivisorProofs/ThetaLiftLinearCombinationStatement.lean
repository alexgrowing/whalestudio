import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLinearCombination
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_linear_combination : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, ∀ (c : ℂ) (h : UA σ G.W.J),
      G.M'.I om' (Φ + c • Ψ) h = G.M'.I om' Φ h + c * G.M'.I om' Ψ h := by
  first | exact @GlobalTheory.ThKSmallLin.smallI_add_smul | exact GlobalTheory.ThKSmallLin.smallI_add_smul | (intros; apply GlobalTheory.ThKSmallLin.smallI_add_smul <;> assumption)
