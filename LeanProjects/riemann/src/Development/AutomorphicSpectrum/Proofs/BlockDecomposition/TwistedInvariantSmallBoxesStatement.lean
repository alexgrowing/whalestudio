import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantSmallBoxes
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_invariant_small_boxes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V), v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype) → ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | exact GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_mem_twKer_box <;> assumption)
