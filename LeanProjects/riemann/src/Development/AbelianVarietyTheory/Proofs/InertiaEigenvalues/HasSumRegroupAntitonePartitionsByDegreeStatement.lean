import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRegroupAntitonePartitionsByDegree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_regroup_antitonePartitions_by_degree : ∀ {m : ℕ} (G : (Fin m → ℕ) → ℂ),
    (Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) →
    Summable (fun d => ‖∑ l ∈ GlobalTheory.JSW.antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ GlobalTheory.JSW.antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  first | exact @GlobalTheory.JSW.regroup_antiParts | exact GlobalTheory.JSW.regroup_antiParts | (intros; apply GlobalTheory.JSW.regroup_antiParts <;> assumption)
