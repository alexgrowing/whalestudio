import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem eInf_mul_eFin : eInf D * eFin D = 0 := by
  simp only [eInf, eFin, pairA]
  first
  | exact Prod.ext (mul_zero _) (zero_mul _)
  | (refine Prod.ext ?_ ?_ <;> simp)

theorem eInf_add_eFin : eInf D + eFin D = 1 := by
  simp only [eInf, eFin, pairA]
  first
  | exact Prod.ext (add_zero _) (zero_add _)
  | (refine Prod.ext ?_ ?_ <;> simp)

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by

  unfold cA sigR
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a b
    simp [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul]
  · intro x y hx hy
    rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem hO_smul_right (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = c • hO S T x y := by

  simp only [hO, Finset.smul_sum, Matrix.smul_apply, Pi.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc]

theorem hO_smul_left (c : AF D.host.F) (x y : WO S T) : hO S T (c • x) y = c • hO S T x y := by

  simp only [hO, Finset.smul_sum, Matrix.smul_apply, Pi.smul_apply, mul_smul_comm, smul_mul_assoc]

theorem symplOH_smul_right (c : AF D.host.F) (x y : WO S T) : symplOH S T x (c • y) = c * symplOH S T x y := by

  simp only [symplOH, symplO, hO_smul_right, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplOH_smul_left (c : AF D.host.F) (x y : WO S T) : symplOH S T (c • x) y = c * symplOH S T x y := by

  simp only [symplOH, symplO, hO_smul_left, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem symplOH_snd (x y : WO S T) (hy : eInf D • y = y) : (symplOH S T x y).2 = 0 := by

  rw [← hy, symplOH_smul_right]
  simp only [eInf, pairA]
  first
  | exact zero_mul _
  | simp

theorem symplOH_fin_real (u y : WO S T) (hu : eFin D • u = u) (hy : eInf D • y = y) : symplOH S T u y = 0 := by

  rw [← hu, ← hy, symplOH_smul_left, symplOH_smul_right, ← mul_assoc, mul_comm (eFin D) (eInf D), eInf_mul_eFin,
    zero_mul]

theorem symplOH_real_fin (y u : WO S T) (hy : eInf D • y = y) (hu : eFin D • u = u) : symplOH S T y u = 0 := by

  rw [← hy, ← hu, symplOH_smul_left, symplOH_smul_right, ← mul_assoc, eInf_mul_eFin, zero_mul]

theorem wo_real_iff (w : WO S T) : w.map (finPart D) = 0 ↔ eInf D • w = w := by
  constructor
  · intro h
    ext i j
    exact (finPart_eq_zero_iff_smul (w i j)).mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact (finPart_eq_zero_iff_smul (w i j)).mpr (congrFun (congrFun h i) j)

theorem wo_fin_iff (w : WO S T) : w.map (infPart D) = 0 ↔ eFin D • w = w := by
  constructor
  · intro h
    ext i j
    exact (infPart_eq_zero_iff_smul (w i j)).mp (congrFun (congrFun h i) j)
  · intro h
    ext i j
    exact (infPart_eq_zero_iff_smul (w i j)).mpr (congrFun (congrFun h i) j)

theorem eFin_smul_sub (w : WO S T) : w - eInf D • w = eFin D • w := by

  rw [eq_sub_of_add_eq' (eInf_add_eFin (D := D)), sub_smul, one_smul]

end Formalism.IndefR.Eqv

end
