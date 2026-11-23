import Mathlib

open scoped Classical

noncomputable def UpperTheory.Reformulated.B.P9.IsReps.{u_1} :
    {V : Type u_1} → [inst : AddCommGroup V] → AddSubgroup V → AddSubgroup V → Finset V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] (Λ₁ Λ₂ : AddSubgroup V) (S : Finset V) ↦
      (∀ x ∈ S, x ∈ Λ₂) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ₁ → x = y) ∧ ∀ y ∈ Λ₂, ∃ x ∈ S, y - x ∈ Λ₁

theorem UpperTheory.Reformulated.B.P9.aux2 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a b : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} →
        b ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} → a + b ∈ Λ ∧ (p : V → V) (a + b) = a + b := by
  intro V _ p Λ a b ha hb
  exact ⟨Λ.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2]⟩

theorem UpperTheory.Reformulated.B.P9.aux3 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V), (0 : V) ∈ Λ ∧ (p : V → V) (0 : V) = (0 : V) := by
  intro V _ p Λ
  exact ⟨Λ.zero_mem, map_zero p⟩

theorem UpperTheory.Reformulated.B.P9.aux4 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} → -a ∈ Λ ∧ (p : V → V) (-a) = -a := by
  intro V _ p Λ a ha
  exact ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2]⟩

noncomputable def UpperTheory.Reformulated.B.P9.partP :
    {V : Type} → [inst : AddCommGroup V] → (V →+ V) → AddSubgroup V → AddSubgroup V :=
    fun {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) ↦
      { carrier := {x : V | x ∈ Λ ∧ (p : V → V) x = x}, add_mem' := @UpperTheory.Reformulated.B.P9.aux2 V inst p Λ,
        zero_mem' := UpperTheory.Reformulated.B.P9.aux3 p Λ, neg_mem' := @UpperTheory.Reformulated.B.P9.aux4 V inst p Λ : AddSubgroup V }

theorem UpperTheory.Reformulated.B.P9.aux6 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a b : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} →
        b ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} → a + b ∈ Λ ∧ (p : V → V) (a + b) = (0 : V) := by
  intro V _ p Λ a b ha hb
  exact ⟨Λ.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩

theorem UpperTheory.Reformulated.B.P9.aux7 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V), (0 : V) ∈ Λ ∧ (p : V → V) (0 : V) = (0 : V) := by
  intro V _ p Λ
  exact ⟨Λ.zero_mem, map_zero p⟩

theorem UpperTheory.Reformulated.B.P9.aux8 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} → -a ∈ Λ ∧ (p : V → V) (-a) = (0 : V) := by
  intro V _ p Λ a ha
  exact ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2, neg_zero]⟩

noncomputable def UpperTheory.Reformulated.B.P9.partQ :
    {V : Type} → [inst : AddCommGroup V] → (V →+ V) → AddSubgroup V → AddSubgroup V :=
    fun {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) ↦
      { carrier := {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)}, add_mem' := @UpperTheory.Reformulated.B.P9.aux6 V inst p Λ,
        zero_mem' := UpperTheory.Reformulated.B.P9.aux7 p Λ, neg_mem' := @UpperTheory.Reformulated.B.P9.aux8 V inst p Λ : AddSubgroup V }

theorem UpperTheory.Reformulated.B.P9.reps_prod :
    ∀ {V : Type} [inst : AddCommGroup V] [_root_.Module ℂ V] {M Λ : AddSubgroup V} (p : V →+ V),
      (∀ (x : V), (p : V → V) ((p : V → V) x) = (p : V → V) x) →
        (∀ x ∈ Λ, (p : V → V) x ∈ Λ) →
          (∀ x ∈ M, (p : V → V) x ∈ M) →
            ∀ {A B : Finset V},
              UpperTheory.Reformulated.B.P9.IsReps M (UpperTheory.Reformulated.B.P9.partP p Λ) A →
                UpperTheory.Reformulated.B.P9.IsReps M (UpperTheory.Reformulated.B.P9.partQ p Λ) B →
                  UpperTheory.Reformulated.B.P9.IsReps M Λ (Finset.image (fun (w : V × V) ↦ w.1 + w.2) (A ×ˢ B)) := by
  intro V _ _ M Λ p hpp hΛ hM A B hA hB
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hA1' : ∀ x ∈ A, x ∈ Λ ∧ p x = x := hA1
  have hB1' : ∀ x ∈ B, x ∈ Λ ∧ p x = 0 := hB1
  have hA3' : ∀ y, (y ∈ Λ ∧ p y = y) → ∃ x ∈ A, y - x ∈ M := hA3
  have hB3' : ∀ y, (y ∈ Λ ∧ p y = 0) → ∃ x ∈ B, y - x ∈ M := hB3
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨a, b⟩, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hw
    exact Λ.add_mem (hA1' a ha).1 (hB1' b hb).1
  · intro x hx y hy hxy
    obtain ⟨⟨a, b⟩, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hw
    obtain ⟨⟨a', b'⟩, hw', rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨ha', hb'⟩ := Finset.mem_product.1 hw'
    change a + b - (a' + b') ∈ M at hxy
    change a + b = a' + b'
    have h1 : p (a + b - (a' + b')) = a - a' := by
      rw [map_sub, map_add, map_add, (hA1' a ha).2, (hA1' a' ha').2, (hB1' b hb).2,
        (hB1' b' hb').2, add_zero, add_zero]
    have h2 : a = a' := hA2 a ha a' ha' (h1 ▸ hM _ hxy)
    have h3 : b = b' := by
      refine hB2 b hb b' hb' ?_
      rwa [h2, add_sub_add_left_eq_sub] at hxy
    rw [h2, h3]
  · intro y hy
    obtain ⟨a, ha, hya⟩ := hA3' (p y) ⟨hΛ y hy, hpp y⟩
    obtain ⟨b, hb, hyb⟩ := hB3' (y - p y)
      ⟨Λ.sub_mem hy (hΛ y hy), by rw [map_sub, hpp, sub_self]⟩
    refine ⟨a + b, Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩, ?_⟩
    have h : y - (a + b) = (p y - a) + (y - p y - b) := by abel
    rw [h]
    exact M.add_mem hya hyb
