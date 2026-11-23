import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SqChartCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem rmulFacts_holds : RmulFacts := by
  intro D X
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (TupI X) :=
    PI.AprimeInfT.borelSpace_tup (F := X.B.I.F) (E := X.B.I.E) (Ainf X.B.I.F) (D.R.rS + 1 + D.R.rS)
  have hcont : ∀ a : MfI X, Continuous (rmulT X a) := by
    intro a
    unfold rmulT
    refine continuous_pi fun b => continuous_pi fun i => ?_
    exact continuous_finset_sum _ fun c _ => continuous_const.mul ((continuous_apply i).comp (continuous_apply c))
  refine ⟨fun a => (hcont a).measurable, ?_, ?_, ?_, ?_, ?_, fun K hK => hK.isClosed.measurableSet, hcont⟩
  · intro a b Y
    funext b' i
    simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · intro g a Y
    funext b i
    show ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL _ _) : Matrix _ _ _).mulVec (rmulT X a Y b) i =
      ∑ c, a c b * ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL _ _) : Matrix _ _ _).mulVec (Y c) i
    simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · intro a Y
    exact sq_gramR_rmul (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J a Y
  · intro a b
    simp only [cTI, Matrix.map_mul, Matrix.transpose_mul]
  · simp only [cTI, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PI.AprimeInfW
