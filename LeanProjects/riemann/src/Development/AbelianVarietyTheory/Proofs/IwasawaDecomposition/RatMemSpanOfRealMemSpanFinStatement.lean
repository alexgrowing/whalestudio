import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatMemSpanOfRealMemSpanFin
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_mem_span_of_real_mem_span_fin : ∀ (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ), (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) → v ∈ Submodule.span ℚ (Set.range w) := by
  first | exact @GlobalTheory.rat_mem_span_of_real_mem_span | exact GlobalTheory.rat_mem_span_of_real_mem_span | (intros; apply GlobalTheory.rat_mem_span_of_real_mem_span <;> assumption)
