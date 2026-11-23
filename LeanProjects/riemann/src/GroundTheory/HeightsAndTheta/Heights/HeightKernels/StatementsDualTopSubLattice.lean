import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeBasisExists
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def DualTopSubLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice F'))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II → F'.lattice ≤ F.lattice →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F'.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def twoVecExample : Fin 1 → ℚ := fun _ => 2

def HermLattice.twiceStandardExample : HermLattice ℚ 1 where
  lattice := Submodule.span (𝓞 ℚ) {twoVecExample}
  fg := Submodule.fg_span (Set.finite_singleton _)
  span_eq := by
    rw [Submodule.span_span_of_tower]
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = (x 0 / 2) • twoVecExample := by
      funext j
      fin_cases j
      simp [twoVecExample]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

theorem twiceStandardExample_le :
    HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice := by
  show Submodule.span (𝓞 ℚ) {twoVecExample} ≤ _
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have h : twoVecExample = (2 : 𝓞 ℚ) • (Pi.single 0 1 : Fin 1 → ℚ) := by
    funext j
    fin_cases j
    simp [twoVecExample, Algebra.smul_def, map_ofNat]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

example : ∃ (T : Type) (_ : Fintype T) (_ : DecidableEq T)
    (b' : Module.Basis T ℤ (dualLattice HermLattice.twiceStandardExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b')) ∧
      Function.Bijective (Matrix.mulVecLin
        (dualEmbMatrix (F := HermLattice.standard ℚ 1) dualBasisStandard)) ∧
      HermLattice.twiceStandardExample.lattice ≤ (HermLattice.standard ℚ 1).lattice ∧ 1 ≤ 1 := by
  obtain ⟨T, hT, hdT, ⟨b'⟩⟩ := DualLatticeBasisExists.proof ℚ 1 HermLattice.twiceStandardExample
  exact ⟨T, hT, hdT, b', DualEmbBijective.proof ℚ 1 _ T b', dualEmbMatrix_standard_bijective,
    twiceStandardExample_le, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
