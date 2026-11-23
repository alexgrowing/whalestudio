import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieAlgebraExpGenerators
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_algebra_exp_generators : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (S : Set 𝔸), IsClosed S → (1 : 𝔸) ∈ S →
    (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) → (∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) →
    ∀ (d : ℕ) (Z : Fin d → 𝔸), (∀ (i : Fin d) (t : ℝ), NormedSpace.exp (t • Z i) ∈ S) →
    (∀ Y : 𝔸, (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ S) → Y ∈ Submodule.span ℝ (Set.range Z)) →
    ∃ s : 𝔸 → Fin d → ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s 1 ∧
      ∀ᶠ X in nhds (1 : 𝔸), X ∈ S → X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  first | exact @GlobalTheory.ClosedMonoid.coords_second_kind_of_spanning | exact GlobalTheory.ClosedMonoid.coords_second_kind_of_spanning | (intros; apply GlobalTheory.ClosedMonoid.coords_second_kind_of_spanning <;> assumption)
