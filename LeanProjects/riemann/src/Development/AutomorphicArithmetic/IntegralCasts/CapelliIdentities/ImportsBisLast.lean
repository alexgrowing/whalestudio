import Mathlib

def UpperTheory.Reformulated.B.RepresentationStabilizer.stab {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G U) (u : U) : Subgroup G where
  carrier := {g | ρ g u = u}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc ρ a⁻¹ u = ρ a⁻¹ (ρ a u) := by rw [ha]
      _ = u := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
