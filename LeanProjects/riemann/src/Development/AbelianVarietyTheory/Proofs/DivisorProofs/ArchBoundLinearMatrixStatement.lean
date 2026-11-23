import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundLinearMatrix
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_bound_linear_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (κ : Type) [Fintype κ]
    (f : (κ → AF F) × (κ → AF F) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E)), ∃ K : ℝ, 0 ≤ K ∧
    ∀ (v : (κ → AF F) × (κ → AF F)) (B : ℝ), 0 ≤ B → (∀ w i, ‖archAt F w (v.1 i)‖ ≤ B ∧ ‖archAt F w (v.2 i)‖ ≤ B) →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) k l, ‖piInf τ (f v k l)‖ ≤ K * B := by
  first | exact @GlobalTheory.ThetaDecay.linMap_archBound | exact GlobalTheory.ThetaDecay.linMap_archBound | (intros; apply GlobalTheory.ThetaDecay.linMap_archBound <;> assumption)
