import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfMemSpanRingOfIntegersMapNumberField
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_mem_span_ringOfIntegers_map_numberField : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') (n : ℕ)
    (N : Submodule (𝓞 K) (Fin n → K)) (w : Fin n → K),
    (fun i => j (w i)) ∈ Submodule.span (𝓞 K') ((fun (c : Fin n → K) i => j (c i)) '' (N : Set (Fin n → K))) → w ∈ N := by
  first | exact @GlobalTheory.FlatDescent.mem_of_mem_span_map | exact GlobalTheory.FlatDescent.mem_of_mem_span_map | (intros; apply GlobalTheory.FlatDescent.mem_of_mem_span_map <;> assumption)
