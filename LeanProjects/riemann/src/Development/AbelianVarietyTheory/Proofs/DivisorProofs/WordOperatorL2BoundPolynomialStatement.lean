import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordOperatorL2BoundPolynomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_operator_L2_bound_polynomial : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ), ∀ Φ ∈ schA F κ, ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ P : ℕ, ∃ C : ℝ, ∀ ρ : ℝ, 1 ≤ ρ → ∀ zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), zs.length ≤ P → (∀ ζ ∈ zs, ‖ζ‖ ≤ ρ) → ∫⁻ x, ‖wordR F T c zs Φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (C * ρ ^ (2 * P)) := by
  first | exact @GlobalTheory.ArchDecay.wordR_L2_le | exact GlobalTheory.ArchDecay.wordR_L2_le | (intros; apply GlobalTheory.ArchDecay.wordR_L2_le <;> assumption)
