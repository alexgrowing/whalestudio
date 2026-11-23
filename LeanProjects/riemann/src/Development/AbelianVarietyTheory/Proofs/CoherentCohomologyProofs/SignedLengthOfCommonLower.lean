import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
universe u_1 u_2

namespace GlobalTheory.RelativeLengthAdditivity

open GlobalTheory

section
variable {S : Type u_1} {V : Type u_2} [Ring S] [AddCommGroup V] [Module S V]

theorem relLength_bot_add {A D : Submodule S V} (h : D ≤ A) :
    relLength A ⊥ = relLength A D + relLength D ⊥ := by
  let N : Submodule S A := D.submoduleOf A
  have hex := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N)
  have hN : Module.length S N = relLength D ⊥ := by
    have := relLength_submoduleOf h (⊥ : Submodule S V)
    have hb : (⊥ : Submodule S V).submoduleOf A = ⊥ := by
      ext x; simp [Submodule.submoduleOf]
    rw [hb, relLength_bot_right] at this
    exact this
  rw [relLength_bot_right, hex, hN, add_comm]
  rfl

theorem relLength_add {A C D : Submodule S V} (hCD : C ≤ D) (hDA : D ≤ A) :
    relLength A C = relLength A D + relLength D C := by
  have hb : C.map C.mkQ = ⊥ := Submodule.mkQ_map_self C
  rw [← relLength_map_mkQ le_rfl A, ← relLength_map_mkQ hCD A, ← relLength_map_mkQ le_rfl D, hb]
  exact relLength_bot_add (Submodule.map_mono hDA)

theorem signedLength_of_common_lower : ∀ {S : Type u_1} {V : Type u_2} [inst : Ring S] [inst_1 : AddCommGroup V]
    [inst_2 : Module S V] {A B C : Submodule S V}, C ≤ A → C ≤ B → ∀ {m n : ℕ},
    GlobalTheory.relLength A C = (↑m : ℕ∞) → GlobalTheory.relLength B C = (↑n : ℕ∞) →
    GlobalTheory.LengthCommensurable A B ∧ GlobalTheory.signedLength A B = (↑m : ℤ) - (↑n : ℤ) := by
  intro S V _ _ _ A B C hCA hCB m n hm hn
  have hCD : C ≤ A ⊓ B := le_inf hCA hCB
  have h1 := relLength_add hCD (inf_le_left : A ⊓ B ≤ A)
  have h2 := relLength_add hCD (inf_le_right : A ⊓ B ≤ B)
  rw [relLength_inf_right] at h1
  rw [relLength_inf_right'] at h2
  rw [hm] at h1
  rw [hn] at h2
  have ha : relLength A B ≠ ⊤ := fun h => by simp [h] at h1
  have hb : relLength B A ≠ ⊤ := fun h => by simp [h] at h2
  have hk : relLength (A ⊓ B) C ≠ ⊤ := fun h => by simp [h] at h1
  refine ⟨⟨ha, hb⟩, ?_⟩
  obtain ⟨a, ha'⟩ := ENat.ne_top_iff_exists.mp ha
  obtain ⟨b, hb'⟩ := ENat.ne_top_iff_exists.mp hb
  obtain ⟨k, hk'⟩ := ENat.ne_top_iff_exists.mp hk
  rw [← ha', ← hk'] at h1
  rw [← hb', ← hk'] at h2
  have e1 : m = a + k := by exact_mod_cast h1
  have e2 : n = b + k := by exact_mod_cast h2
  rw [signedLength_eq_of_relLength_eq ha'.symm hb'.symm, e1, e2]
  push_cast
  ring
end

end GlobalTheory.RelativeLengthAdditivity

example : ∀ {S : Type u_1} {V : Type u_2} [inst : Ring S] [inst_1 : AddCommGroup V] [inst_2 : Module S V] {A B C : Submodule S V}, C ≤ A → C ≤ B → ∀ {m n : ℕ}, GlobalTheory.relLength A C = (↑m : ℕ∞) → GlobalTheory.relLength B C = (↑n : ℕ∞) → GlobalTheory.LengthCommensurable A B ∧ GlobalTheory.signedLength A B = (↑m : ℤ) - (↑n : ℤ) := @GlobalTheory.RelativeLengthAdditivity.signedLength_of_common_lower
