import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisDisj

variable {D : D7}

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rw [TensorProduct.smul_tmul']; rfl
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]

theorem hO_add_left (S T : HSp D) (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  simp only [hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  simp only [hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_smul_smul (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) :
    hO S T (c • x) (c' • y) = (c * c') • hO S T x y := by
  simp only [hO, Matrix.smul_apply, cA_smul, Finset.smul_sum, mul_smul_comm, smul_mul_assoc, smul_smul]

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO, hO_add_left, mul_add, map_add]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO, hO_add_right, mul_add, map_add]

theorem symplOH_smul_smul_eq_zero (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (h : c * c' = 0) :
    symplOH S T (c • x) (c' • y) = 0 := by
  rw [symplOH, symplO, hO_smul_smul, h, zero_smul, mul_zero, map_zero, mul_zero]

theorem heisO_smul_add_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c c' : AF D.host.F) (x y : WO S T) (f : WO S T → ℂ), c * c' = 0 → heisO ψ S T (c • x + c' • y) f = heisO ψ S T (c • x) (heisO ψ S T (c' • y) f) := by
  intro D ψ S T c c' x y f h
  funext w
  simp only [heisO]
  rw [symplOH_add_right, symplOH_add_left, symplOH_smul_smul_eq_zero S T c c' x y h, add_zero,
    AddChar.map_add_eq_mul, add_assoc, mul_assoc]

end GlobalTheory.HeisDisj
