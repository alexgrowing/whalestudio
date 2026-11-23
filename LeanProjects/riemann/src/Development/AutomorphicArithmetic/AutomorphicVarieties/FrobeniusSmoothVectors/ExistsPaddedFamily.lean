import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_padded_family {κ M : Type} [Finite κ] [Zero M] (q : κ → Prop) (f : κ → M) (n : ℕ)
    (h : Nat.card {u // q u} ≤ n) :
    ∃ G : Fin n → M, (∀ i, G i = 0 ∨ ∃ u, q u ∧ G i = f u) ∧ ∀ u, q u → ∃ i, G i = f u := by
  classical
  haveI := Fintype.ofFinite κ
  have hc : Fintype.card {u // q u} ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨Function.extend e (fun u => f u.1) 0, ?_, ?_⟩
  · intro i
    by_cases hi : ∃ u, e u = i
    · obtain ⟨u, rfl⟩ := hi
      right
      exact ⟨u.1, u.2, by rw [e.injective.extend_apply]⟩
    · left
      rw [Function.extend_apply' _ _ _ hi]
      rfl
  · intro u hu
    exact ⟨e ⟨u, hu⟩, by rw [e.injective.extend_apply]⟩

theorem UpperTheory.V.Fr.ep_pad :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} (S : Space O F 3) (x : Ideal S.A) (L : S.Loc x) (σ : L.R →ₐ[L.O'] L.R), L.IsInv σ → ∀ P : GPres L.O' σ, Nat.card {u // P.wf u = 0} + (3 * F.d + 1) ≤ P.a → Nat.card {u // P.wf u = 1} ≤ P.g → L.ρ.ee = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (.inr i))) → Nonempty L.EPres := by
  intro l _ O _ _ F S x L σ hσ P h0 h1 hee
  obtain ⟨Fe, hF, hF'⟩ := exists_padded_family (fun u => P.wf u = 0) P.f (P.a - (3 * F.d + 1)) (by omega)
  obtain ⟨Go, hG, hG'⟩ := exists_padded_family (fun u => P.wf u = 1) P.f P.g h1
  have two : ∀ j : ZMod 2, j = 0 ∨ j = 1 := by decide
  refine ⟨{ a := P.a, b := P.a - (3 * F.d + 1), g := P.g, p := P.p, Fe := Fe, Go := Go,
            num := by omega, surj := P.surj, ker := ?_, even := ?_, odd := ?_, min := P.min,
            ent := ?_, base := ?_, ee := hee }⟩
  · rw [P.ker]
    apply le_antisymm
    · apply Ideal.span_mono
      rintro _ ⟨u, rfl⟩
      rcases two (P.wf u) with h | h
      · exact Or.inl (hF' u h)
      · exact Or.inr (hG' u h)
    · rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · rcases hF i with h | ⟨u, -, h⟩
        · rw [h]; exact Ideal.zero_mem _
        · rw [h]; exact Ideal.subset_span ⟨u, rfl⟩
      · rcases hG i with h | ⟨u, -, h⟩
        · rw [h]; exact Ideal.zero_mem _
        · rw [h]; exact Ideal.subset_span ⟨u, rfl⟩
  · intro i
    rcases hF i with h | ⟨u, hu, h⟩
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← hu]; exact P.hf u
  · intro i
    rcases hG i with h | ⟨u, hu, h⟩
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← hu]; exact P.hf u
  · intro s i j
    rw [P.part]
    exact hσ.ent s i j
  · intro y
    rw [P.part]
    exact hσ.base y
