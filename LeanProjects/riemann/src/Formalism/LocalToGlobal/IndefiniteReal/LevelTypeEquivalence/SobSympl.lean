import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SymplOHSmulRight

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem symplOH_add_right (x y y' : WO S T) : symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO, Matrix.add_apply, RingHom.map_add, mul_add, add_mul, Finset.sum_add_distrib,
    LinearMap.map_add]

theorem symplOH_add_left (x x' y : WO S T) : symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, LinearMap.map_add]

def cAlin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := fun x y => RingHom.map_add _ x y
  map_smul' := fun c z => cA_smul c z

theorem continuous_cA : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cAlin D)

theorem continuous_trace : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))

set_option maxHeartbeats 1000000 in
theorem continuous_hO : Continuous fun p : WO S T × WO S T => hO S T p.1 p.2 := by
  have hc := continuous_cA (D := D)
  unfold hO
  fun_prop

theorem continuous_symplOH : Continuous fun p : WO S T × WO S T => symplOH S T p.1 p.2 := by
  have h1 : Continuous fun p : WO S T × WO S T => symplO S T p.1 p.2 :=
    continuous_trace.comp (continuous_const.mul continuous_hO)
  exact continuous_const.mul h1

set_option maxHeartbeats 1000000 in
theorem continuous_hO_right (x : WO S T) : Continuous fun y : WO S T => hO S T x y := by
  have hc := continuous_cA (D := D)
  unfold hO
  fun_prop

theorem continuous_symplOH_right (x : WO S T) : Continuous (symplOH S T x) := by
  have h1 : Continuous fun y : WO S T => symplO S T x y :=
    continuous_trace.comp (continuous_const.mul (continuous_hO_right x))
  exact continuous_const.mul h1

set_option maxHeartbeats 1000000 in
theorem continuous_hO_left (y : WO S T) : Continuous fun x : WO S T => hO S T x y := by
  unfold hO
  fun_prop

theorem continuous_symplOH_left (y : WO S T) : Continuous fun x => symplOH S T x y := by
  have h1 : Continuous fun x : WO S T => symplO S T x y :=
    continuous_trace.comp (continuous_const.mul (continuous_hO_left y))
  exact continuous_const.mul h1

end Formalism.IndefR.Eqv

end
