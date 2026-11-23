import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem twKer_one_mem_aug_stage : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (U : Subgroup G) (N : ℕ → Set G), Monotone N →
    (∀ y ∈ U, ∃ m, y ∈ N m) → ∀ v ∈ twKer π U 1, ∃ m, v ∈ aug π (N m) (fun _ => 1) := by
  intro G V _ _ _ π U N hN hU v hv
  have mono : ∀ {a b : ℕ}, a ≤ b → aug π (N a) (fun _ => 1) ≤ aug π (N b) (fun _ => 1) := by
    intro a b h
    refine Submodule.span_mono ?_
    rintro x ⟨g, hg, w, rfl⟩
    exact ⟨g, hN h hg, w, rfl⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, w, rfl⟩ := hx
    obtain ⟨m, hm⟩ := hU n n.2
    exact ⟨m, Submodule.subset_span ⟨n, hm, w, by simp⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, add_mem (mono (le_max_left _ _) ha) (mono (le_max_right _ _) hb)⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, Submodule.smul_mem _ c ha⟩

end GlobalTheory.PsType
