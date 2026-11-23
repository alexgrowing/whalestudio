import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

def HermLattice.withStdMetric {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    HermLattice K i where
  lattice := F.lattice
  fg := F.fg
  span_eq := F.span_eq
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

def DualTopMetricChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F b hb) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - F.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopLatticeChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T T' : Type) [Fintype T]
    [DecidableEq T] [Fintype T'] [DecidableEq T'] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice (HermLattice.standard K i)))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) =
      II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine (HermLattice.standard K i) b' hb') -
        F.withStdMetric.degree *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def DualTopStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine (HermLattice.standard K i) b hb) =
      (Module.finrank ℚ K : ℝ) *
        II (Fin 1) (plBlocks 1 1 (i - 1)) (grassIdeal 1 1 (i - 1)) (1 * 1 * (i - 1) + 1)
          (fun _ => fsMulti (plBlocks 1 1 (i - 1)))

def DualGeomDegStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
      (Module.finrank ℚ K : ℝ) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

def HermLattice.scaledExample : HermLattice ℚ 1 where
  lattice := (HermLattice.standard ℚ 1).lattice
  fg := (HermLattice.standard ℚ 1).fg
  span_eq := (HermLattice.standard ℚ 1).span_eq
  metric := fun _ => Matrix.diagonal fun _ => (4 : ℂ)
  posDef := fun _ => Matrix.PosDef.diagonal fun _ => by norm_num
  conj := fun _ => by
    ext a c
    by_cases h : a = c <;> simp [h, map_ofNat]

example : Function.Bijective (Matrix.mulVecLin
    (dualEmbMatrix (F := HermLattice.scaledExample) dualBasisStandard)) :=
  dualEmbMatrix_standard_bijective

example : Function.Bijective (Matrix.mulVecLin
    (dualEmbMatrix (F := HermLattice.scaledExample.withStdMetric) dualBasisStandard)) :=
  dualEmbMatrix_standard_bijective

example : HermLine (dualBlocks Unit) × HermLine (dualBlocks Unit) × HermLine (dualBlocks Unit) ×
    PLift (1 ≤ 1) :=
  ⟨dualLine HermLattice.scaledExample dualBasisStandard dualEmbMatrix_standard_bijective,
    dualLine HermLattice.scaledExample.withStdMetric dualBasisStandard dualEmbMatrix_standard_bijective,
    dualLine (HermLattice.standard ℚ 1) dualBasisStandard dualEmbMatrix_standard_bijective, ⟨le_rfl⟩⟩

end

end GroundTheory.Heights₂.Heights
