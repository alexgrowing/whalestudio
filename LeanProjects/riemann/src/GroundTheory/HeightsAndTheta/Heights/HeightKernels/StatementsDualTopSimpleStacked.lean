import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleSub
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopStacked
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualTopSimpleStacked.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (a : T → ℤ) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    II Unit (dualBlocks T) (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (∑ t, Real.log |(a t : ℝ)|) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

open DualTopSimpleSubExample in

example : ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T)
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard ℚ 1)))
    (b' : Module.Basis T ℤ (dualLattice HermLattice.twiceStandardExample)) (a : T → ℤ),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧
      Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')) ∧
      HermLattice.twiceStandardExample.lattice < (HermLattice.standard ℚ 1).lattice ∧
      (∀ N : Submodule (𝓞 ℚ) (Fin 1 → ℚ), HermLattice.twiceStandardExample.lattice ≤ N →
        N ≤ (HermLattice.standard ℚ 1).lattice →
        N = HermLattice.twiceStandardExample.lattice ∨ N = (HermLattice.standard ℚ 1).lattice) ∧
      (∀ t, (b t : Fin 1 → ℚ) = a t • (b' t : Fin 1 → ℚ)) ∧ 1 ≤ 1 := by
  obtain ⟨T', hT', hdT', ⟨b'⟩⟩ := DualLatticeBasisExists.proof ℚ 1 HermLattice.twiceStandardExample
  have hcard : Fintype.card Unit = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective dualBasisStandard dualEmbMatrix_standard_bijective,
      DualTopStackedExistence.card_eq_of_bijective b' (DualEmbBijective.proof ℚ 1 _ T' b')]
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked twiceStandardExample_le
    dualBasisStandard b' hcard
  exact ⟨T', hT', hdT', b₁, b₁', a, DualEmbBijective.proof ℚ 1 _ T' b₁,
    DualEmbBijective.proof ℚ 1 _ T' b₁', twice_lt, twice_cover, hab, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
