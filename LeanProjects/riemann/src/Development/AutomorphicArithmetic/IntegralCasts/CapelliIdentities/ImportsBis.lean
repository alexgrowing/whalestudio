import Mathlib

theorem UpperTheory.Reformulated.B.DYdc4.main :
    ∀ (n a : ℕ) (G : Finset (Fin n)),
      G.card = a → ∃ (τ : Equiv.Perm (Fin n)), ∀ (j : Fin n), (↑j : ℕ) < a ↔ (τ : Fin n → Fin n) j ∈ G := by
  intro n a G hG
  have ha : a ≤ n := by
    have h := G.card_le_univ
    rw [Fintype.card_fin, hG] at h
    exact h
  have hp : Fintype.card {x : Fin n // (x : ℕ) < a} = a := by
    have e : Fin a ≃ {x : Fin n // (x : ℕ) < a} :=
      { toFun := fun i => ⟨Fin.castLE ha i, i.isLt⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun i => rfl
        right_inv := fun x => rfl }
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hq : Fintype.card {x : Fin n // x ∈ G} = a := by
    rw [Fintype.card_coe, hG]
  let e : {x : Fin n // (x : ℕ) < a} ≃ {x : Fin n // x ∈ G} :=
    Fintype.equivOfCardEq (hp.trans hq.symm)
  refine ⟨e.extendSubtype, fun j => ⟨fun h => e.extendSubtype_mem j h, fun h => ?_⟩⟩
  by_contra h'
  exact e.extendSubtype_not_mem j h' h
