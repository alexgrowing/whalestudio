import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.LiftIdempotentFactorizationHolds
import Development.EtaleCohomology.EtaleSheaves.FiniteChartSurjPf
import Development.EtaleCohomology.EtaleSheaves.HensIdemCut
import Development.EtaleCohomology.EtaleSheaves.LChartPf
import Development.EtaleCohomology.EtaleSheaves.LEtaleLiftPf
import Development.EtaleCohomology.EtaleSheaves.LFactorPf
import Development.EtaleCohomology.EtaleSheaves.LIdemLiftPf
import Development.EtaleCohomology.EtaleSheaves.LIdemPf
import Development.EtaleCohomology.EtaleSheaves.LJacPf
import Development.EtaleCohomology.EtaleSheaves.LMonicPf
import Development.EtaleCohomology.EtaleSheaves.SurjectiveCharts.EtaleSurjectiveChartOfFiniteChartSurj

namespace UpperTheory.Et.HenselianIdempotents

theorem a0 : LateralTheory.E.HensIdemCut.LJac := LateralTheory.E.LJacPf.LJac_of
theorem a1 : LateralTheory.E.HensIdemCut.LMonic := LateralTheory.E.LMonicPf.LMonic_of
theorem a2 : LateralTheory.E.LIdemLiftPf.LFact := UpperTheory.liftIdempotentFactorization_holds
theorem a3 : LateralTheory.E.LChartPf.LIdemLift := LateralTheory.E.LIdemLiftPf.LIdemLift_of a2
theorem a4 : LateralTheory.E.LSurjChartPf.FiniteChartSurj := LateralTheory.E.FiniteChartSurjPf.FiniteChartSurj_of
theorem a5 : LateralTheory.E.LChartPf.LSurjChart := LateralTheory.E.LSurjChartPf.etale_surjective_chart_of_finite_chart_surj a4
theorem a6 : LateralTheory.E.LEtaleLiftPf.LChart := LateralTheory.E.LChartPf.LChart_of a3 a5
theorem a7 : LateralTheory.E.LFactorPf.LEtaleLift := LateralTheory.E.LEtaleLiftPf.LEtaleLift_of a6
theorem a8 : LateralTheory.E.HensIdemCut.LFactor := LateralTheory.E.LFactorPf.LFactor_of a7
theorem a9 : LateralTheory.E.HensIdemCut.LIdem := LateralTheory.E.LIdemPf.LIdem_of
theorem a10 : LateralTheory.E.t_E1Cut.HensIdem := LateralTheory.E.HensIdemCut.goal_of a0 a1 a8 a9

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.HensIdem := a10

end UpperTheory.Et.HenselianIdempotents
