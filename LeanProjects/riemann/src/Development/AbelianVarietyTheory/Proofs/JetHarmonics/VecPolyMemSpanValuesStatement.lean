import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValues
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_values_of_vector_polynomial : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V) (X : ℕ → V) (ν : Fin n → ℂ), Function.Injective ν → (∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) → (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧ ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  first | exact @GlobalTheory.vecPoly_mem_span_values | exact GlobalTheory.vecPoly_mem_span_values | (intros; apply GlobalTheory.vecPoly_mem_span_values <;> assumption)
