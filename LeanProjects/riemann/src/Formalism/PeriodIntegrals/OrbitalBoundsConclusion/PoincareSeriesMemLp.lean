import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoincareSeriesMeasurability.FoldL2DoubleCoset

theorem fold_l2_bound_b (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesMemLp G μ :=
  PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.fold_L2_double_coset G μ
