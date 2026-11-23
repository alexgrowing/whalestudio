import Mathlib

open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.Topology

theorem finite_image_mk_of_isOpen_of_isCompact :
    ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
      (H : AddSubgroup G) (K : Set G), IsOpen (H : Set G) → IsCompact K →
      (QuotientAddGroup.mk '' K : Set (G ⧸ H)).Finite := by
  intro G _ _ _ H K hH hK
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : G => (fun y => x + y) '' (H : Set G))
    (fun x => (Homeomorph.addLeft x).isOpenMap _ hH)
    (fun x _ => Set.mem_iUnion.2 ⟨x, 0, H.zero_mem, add_zero x⟩)
  refine (t.finite_toSet.image (QuotientAddGroup.mk : G → G ⧸ H)).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨x, hx, hxk⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨h, hh, rfl⟩ := hxk
  refine ⟨x, hx, ?_⟩
  exact QuotientAddGroup.eq.2 (by simpa using hh)

end GlobalTheory.CompanionTheory.Topology
