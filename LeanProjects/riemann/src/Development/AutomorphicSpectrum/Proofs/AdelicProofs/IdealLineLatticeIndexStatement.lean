import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealLineLatticeIndex
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_line_lattice_index : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (M : Submodule (𝓞 K) (Fin n → K)), M.FG → Submodule.span K (M : Set (Fin n → K)) = ⊤ → ∀ v : Fin n → K, v ≠ 0 → ∃ (I : Ideal (𝓞 K)) (d : 𝓞 K), I ≠ ⊥ ∧ d ≠ 0 ∧ (∀ t ∈ I, ((t : K) / (d : K)) • v ∈ M) ∧ genIndex (M ⊓ (Submodule.span K (Set.range fun _ : Fin 1 => v)).restrictScalars (𝓞 K)).toAddSubgroup (Submodule.span (𝓞 K) (Set.range fun _ : Fin 1 => v)).toAddSubgroup = |((Algebra.norm ℚ (d : K) : ℚ) : ℝ)| / (I.absNorm : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.SatLine.saturatedLine_eq_ideal_div | exact GlobalTheory.CompanionTheory.Adelic.SatLine.saturatedLine_eq_ideal_div | (intros; apply GlobalTheory.CompanionTheory.Adelic.SatLine.saturatedLine_eq_ideal_div <;> assumption)
