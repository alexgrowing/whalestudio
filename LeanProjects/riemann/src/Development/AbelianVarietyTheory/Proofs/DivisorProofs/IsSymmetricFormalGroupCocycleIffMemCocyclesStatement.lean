import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocycles
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := by
  first | exact @GlobalTheory.Katz.isCoc_iff_mem_cocycles | exact GlobalTheory.Katz.isCoc_iff_mem_cocycles | (intros; apply GlobalTheory.Katz.isCoc_iff_mem_cocycles <;> assumption)
