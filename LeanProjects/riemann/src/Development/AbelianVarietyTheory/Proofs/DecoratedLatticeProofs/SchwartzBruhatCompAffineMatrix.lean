import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.AffineSB

theorem mem_SB_comp_affine : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [DecidableEq R] [Fintype Q] (A : GL R k) (a : Matrix R Q k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => Φ (A.val * x + a)) ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ R Q _ _ _ A a Φ hΦ
  have hc : ∀ B : Matrix R R k, Continuous fun x : Matrix R Q k => B * x := fun B =>
    continuous_const.matrix_mul continuous_id
  let e : Matrix R Q k ≃ₜ Matrix R Q k :=
    { toFun := fun x => A.val * x + a
      invFun := fun y => (A⁻¹ : GL R k).val * (y - a)
      left_inv := fun x => by
        simp only [add_sub_cancel_right, ← Matrix.mul_assoc, Matrix.coe_units_inv]
        rw [Matrix.nonsing_inv_mul _ (by simpa using A.isUnit.map Matrix.detMonoidHom), Matrix.one_mul]
      right_inv := fun y => by
        simp only [← Matrix.mul_assoc, Matrix.coe_units_inv]
        rw [Matrix.mul_nonsing_inv _ (by simpa using A.isUnit.map Matrix.detMonoidHom), Matrix.one_mul, sub_add_cancel]
      continuous_toFun := (hc _).add continuous_const
      continuous_invFun := (hc _).comp (continuous_id.sub continuous_const) }
  exact ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩

end GlobalTheory.AffineSB
