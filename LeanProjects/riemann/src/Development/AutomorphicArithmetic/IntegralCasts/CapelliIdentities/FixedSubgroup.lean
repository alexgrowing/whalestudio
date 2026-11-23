import Mathlib

noncomputable def UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd :
    {A H M : Type} →
      [inst : CommRing A] →
        [inst_1 : Group H] →
          [inst_2 : AddCommGroup M] → [inst_3 : _root_.Module A M] → Representation A H M → Subgroup H → Submodule A M :=
  fun {_A _H _M} _ _ _ _ ρ K =>
    { carrier := {v | ∀ k ∈ K, ρ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        rw [map_add, ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero (ρ k)
      smul_mem' := fun c v hv k hk => by
        rw [map_smul, hv k hk] }
