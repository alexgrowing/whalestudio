import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB

namespace GlobalTheory.HoweNonsplit

open GlobalTheory.WeilM GlobalTheory.HoweAdelic

theorem isLocSub_sup {Y G H : Type} [Group G] [Group H] [TopologicalSpace Y] {om : G × H →* Module.End ℂ (Y → ℂ)}
    {N N' : Submodule ℂ (Y → ℂ)} (h : IsLocSub om N) (h' : IsLocSub om N') : IsLocSub om (N ⊔ N') := by
  refine ⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun k φ hφ => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hφ
  rw [map_add]
  exact Submodule.add_mem_sup (h.2.2 k y hy) (h'.2.2 k z hz)

end GlobalTheory.HoweNonsplit
