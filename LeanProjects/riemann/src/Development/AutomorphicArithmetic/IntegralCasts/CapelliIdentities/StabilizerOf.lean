import Mathlib

noncomputable def UpperTheory.Reformulated.B.StabilizerOf.stabilizerOf.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] →
        {V : Type u_2} → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G} _ {_V} _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      one_mem' := by
        show ρ 1 v = v
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by rw [inv_mul_cancel, map_one]; rfl }
