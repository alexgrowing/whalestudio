import Mathlib

noncomputable def UpperTheory.Reformulated.B.StabilizerSubgroup.stabG :
    {G V : Type} →
      [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → V → Subgroup G :=
  fun {G _V} _ _ _ ρ v =>
    { carrier := {g : G | ρ g v = v}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        show ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show ρ 1 v = v
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha => by
        have ha' : ρ a v = v := ha
        show ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply] }
