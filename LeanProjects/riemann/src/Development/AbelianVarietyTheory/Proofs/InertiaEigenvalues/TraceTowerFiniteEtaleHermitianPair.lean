import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem trace_tower_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (z : A.L), Algebra.trace F A.K (Algebra.trace A.K A.L z) = Algebra.trace F E (Algebra.trace E A.L z) := by
  intro F E _ _ _ _ hU A z
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  have hE : IsBaseChange E (IsScalarTower.toAlgHom F A.K A.L).toLinearMap := A.push.out
  have hK : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap := A.push.symm.out
  haveI : Module.Free E A.L := Module.Free.of_equiv hE.equiv
  haveI : Module.Finite E A.L := Module.Finite.equiv hE.equiv
  haveI : Module.Free A.K A.L := Module.Free.of_equiv hK.equiv
  haveI : Module.Finite A.K A.L := Module.Finite.equiv hK.equiv
  rw [Algebra.trace_trace, Algebra.trace_trace]

end GlobalTheory
