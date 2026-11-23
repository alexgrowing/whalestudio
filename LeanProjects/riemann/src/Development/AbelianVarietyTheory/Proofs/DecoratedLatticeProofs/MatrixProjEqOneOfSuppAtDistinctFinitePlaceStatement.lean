import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixProjEqOneOfSuppAtDistinctFinitePlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V), q.v ≠ q'.v → SuppAt q'.e V g → (mt V g).map q.pr = 1 := by
  first | exact @GlobalTheory.OtherPlace.mt_map_pr_eq_one | exact GlobalTheory.OtherPlace.mt_map_pr_eq_one | (intros; apply GlobalTheory.OtherPlace.mt_map_pr_eq_one <;> assumption)
