import Mathlib

noncomputable def UpperTheory.Reformulated.B.VectorStabilizer.vecStab :
    {M : Type} →
      [inst : Group M] →
        {X : Type} → [inst_1 : AddCommGroup X] → [inst_2 : _root_.Module ℂ X] → Representation ℂ M X → X → Subgroup M :=
  fun {M} _ {_} _ _ ρ x =>
    { carrier := {g : M | ρ g x = x}
      one_mem' := by
        show ρ 1 x = x
        rw [map_one, Module.End.one_apply]
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        calc ρ a⁻¹ x = ρ a⁻¹ (ρ a x) := by rw [ha']
          _ = ρ (a⁻¹ * a) x := by rw [map_mul, Module.End.mul_apply]
          _ = x := by rw [inv_mul_cancel, map_one, Module.End.one_apply] }
