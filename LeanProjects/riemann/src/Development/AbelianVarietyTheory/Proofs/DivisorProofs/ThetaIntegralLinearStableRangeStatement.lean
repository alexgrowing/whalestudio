import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearStableRange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_linear_stable_range : GlobalTheory.ThK.WeilConv → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → d + 2 * min r s < 2 * n ∨ min r s = 0 →
    ∀ h, ∀ Φ ∈ schA F (Fin n × Fin d), ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ c : ℂ, M.I om (c • Φ + Ψ) h = c * M.I om Φ h + M.I om Ψ h := by
  first | exact @GlobalTheory.ThKLin.I_linear | exact GlobalTheory.ThKLin.I_linear | (intros; apply GlobalTheory.ThKLin.I_linear <;> assumption)
