import Mathlib

namespace Bl.FirstBlockLemmaG

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O] [inst_1 : IsLocalRing.{0} O] {a m : O},
  IsUnit.{0} a → Membership.mem.{0, 0} (IsLocalRing.maximalIdeal.{0} O) m → IsUnit.{0} (HSub.hSub.{0, 0, 0} a m) := by
  intro O _ _ a m ha hm
  by_contra h
  have h1 : a - m ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal (a - m)).mpr (mem_nonunits_iff.mpr h)
  have h2 : a ∈ IsLocalRing.maximalIdeal O := by
    have h3 := Ideal.add_mem _ h1 hm
    rwa [sub_add_cancel] at h3
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal a).mp h2)) ha

end Bl.FirstBlockLemmaG
