import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedBySmallBox
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_by_small_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ v : V, ∃ N : ℤ, ∀ x ∈ box k n N, ρ x v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed <;> assumption)
