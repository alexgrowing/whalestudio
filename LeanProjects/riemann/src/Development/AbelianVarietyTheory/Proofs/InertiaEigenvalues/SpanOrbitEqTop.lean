import Mathlib

namespace GlobalTheory.SpanOrbitTop

theorem span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : Representation.IsIrreducible π) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G ↦ π g v) = ⊤ := by
  have hinv : ∀ (h : G) ⦃x : V⦄, x ∈ Submodule.span ℂ (Set.range fun g : G ↦ π g v) →
      π h x ∈ Submodule.span ℂ (Set.range fun g : G ↦ π g v) := by
    intro h x hx
    have hle : (Submodule.span ℂ (Set.range fun g : G ↦ π g v)).map (π h) ≤
        Submodule.span ℂ (Set.range fun g : G ↦ π g v) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span ⟨h * g, by simp [map_mul]⟩
    exact hle (Submodule.mem_map_of_mem hx)
  let S : Subrepresentation π := ⟨Submodule.span ℂ (Set.range fun g : G ↦ π g v), hinv⟩
  have hvS : v ∈ S.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  have := hπ
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    have hb : v ∈ (⊥ : Subrepresentation π).toSubmodule := h ▸ hvS
    exact hv ((Submodule.mem_bot ℂ).mp hb)
  · exact congrArg Subrepresentation.toSubmodule h

end GlobalTheory.SpanOrbitTop
