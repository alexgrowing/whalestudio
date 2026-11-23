import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isSS_of_sSup_irreducible_eq_top {k Γ : Type} [Field k] [Group Γ] {V : Type}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V)
    (S : Set (Submodule k V))
    (hS : ∀ U ∈ S, Stable ρ U ∧ ∀ U' : Submodule k V, U' ≤ U → Stable ρ U' → U' = ⊥ ∨ U' = U)
    (htop : sSup S = ⊤) : IsSS ρ := by
  have hsup : ∀ A B : Submodule k V, Stable ρ A → Stable ρ B → Stable ρ (A ⊔ B) := by
    intro A B hA hB g v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (hA g a ha) (hB g b hb)
  intro W hW
  obtain ⟨W', ⟨hst, hdis⟩, hmax⟩ :=
    (wellFounded_gt (α := Submodule k V)).has_min {X | Stable ρ X ∧ Disjoint W X}
      ⟨⊥, fun g v hv => by
        rw [(Submodule.mem_bot k).1 hv, map_zero]; exact Submodule.zero_mem _, disjoint_bot_right⟩
  refine ⟨W', hst, hdis, ?_⟩
  rw [codisjoint_iff, eq_top_iff, ← htop, sSup_le_iff]
  intro U hU
  obtain ⟨hUst, hUirr⟩ := hS U hU
  rcases hUirr (U ⊓ (W ⊔ W')) inf_le_left
      (fun g v hv => ⟨hUst g v hv.1, hsup W W' hW hst g v hv.2⟩) with h | h
  · have hd : Disjoint W (W' ⊔ U) :=
      hdis.disjoint_sup_right_of_disjoint_sup_left (by rw [disjoint_comm]; exact disjoint_iff.2 h)
    have hle : ¬ W' < W' ⊔ U := hmax _ ⟨hsup W' U hst hUst, hd⟩
    have heq : W' = W' ⊔ U := eq_of_le_of_not_lt le_sup_left hle
    exact (le_sup_right.trans heq.ge).trans le_sup_right
  · exact h.ge.trans inf_le_right

end GlobalTheory
