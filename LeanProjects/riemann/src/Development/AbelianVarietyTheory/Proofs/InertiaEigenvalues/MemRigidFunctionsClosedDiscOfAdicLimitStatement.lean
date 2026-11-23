import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRigidFunctionsClosedDiscOfAdicLimit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rigidFunctionsClosedDisc_of_adic_limit : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧), (∀ n, s n ∈ R O K l k) → (∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n) → Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0) → f ∈ R O K l k := by
  first | exact @GlobalTheory.mem_R_of_adic_limit | exact GlobalTheory.mem_R_of_adic_limit | (intros; apply GlobalTheory.mem_R_of_adic_limit <;> assumption)
