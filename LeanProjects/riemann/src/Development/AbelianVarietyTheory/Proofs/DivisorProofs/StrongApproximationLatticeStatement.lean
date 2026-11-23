import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (M : ℕ), 0 < M → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ y ∈ latLoc F L v,
    ∃ x ∈ L, (∃ z ∈ latLoc F L v, (fun i => (1 : Fv F v) ⊗ₜ[F] x i) = y + M • z) ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → ∃ z ∈ latLoc F L u, (fun i => (1 : Fv F u) ⊗ₜ[F] x i) = M • z := by
  first | exact @GlobalTheory.LatticeOnePlaceApprox.exists_approx | exact GlobalTheory.LatticeOnePlaceApprox.exists_approx | (intros; apply GlobalTheory.LatticeOnePlaceApprox.exists_approx <;> assumption)
