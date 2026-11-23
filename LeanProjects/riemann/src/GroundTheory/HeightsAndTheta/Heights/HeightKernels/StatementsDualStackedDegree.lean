import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopStacked
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualStackedDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ), F'.lattice ≤ F.lattice → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    F.withStdMetric.degree - F'.withStdMetric.degree = ∑ t, Real.log |(a t : ℝ)|

example : ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T)
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard ℚ 1)))
    (b' : Module.Basis T ℤ (dualLattice HermLattice.twiceStandardExample)) (a : T → ℤ),
      HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice ∧
      ∀ t, (b t : Fin 1 → ℚ) = a t • (b' t : Fin 1 → ℚ) := by
  obtain ⟨T', hT', hdT', ⟨b'⟩⟩ := DualLatticeBasisExists.proof ℚ 1 HermLattice.twiceStandardExample
  have hcard : Fintype.card Unit = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective dualBasisStandard dualEmbMatrix_standard_bijective,
      DualTopStackedExistence.card_eq_of_bijective b' (DualEmbBijective.proof ℚ 1 _ T' b')]
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked twiceStandardExample_le
    dualBasisStandard b' hcard
  exact ⟨T', hT', hdT', b₁, b₁', a, twiceStandardExample_le, hab⟩

end

end GroundTheory.Heights₂.Heights
