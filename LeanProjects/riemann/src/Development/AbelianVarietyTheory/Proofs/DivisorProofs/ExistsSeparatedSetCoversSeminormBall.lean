import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_sep_cover : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
    ∀ R : ℝ, (B R).Finite → ∃ T : Finset G, (T : Set G) ⊆ B R ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → x - y ∉ B 1) ∧
      (B R).encard ≤ T.card * (B 1).encard := by
  intro G _ Λ B hB R hfin
  classical
  let sep : Finset G → Prop := fun T => ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x - y ∉ B 1
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image (hfin.toFinset.powerset.filter sep) Finset.card
    ⟨∅, by simp [sep]⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  obtain ⟨hTS, hTsep⟩ := hT
  have hsub : (T : Set G) ⊆ B R := fun x hx => hfin.mem_toFinset.1 (hTS hx)
  have h0 : (0 : G) ∈ B 1 := hB.zero_mem 1 zero_le_one
  have hsymm : ∀ u, u ∈ B 1 → -u ∈ B 1 := by
    intro u hu
    have := hB.sub_mem 0 1 0 u (hB.zero_mem 0 le_rfl) hu
    simpa using this
  have hcov : ∀ x ∈ B R, ∃ t ∈ T, x - t ∈ B 1 := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact ⟨x, hxT, by simpa using h0⟩
    by_contra hne
    push_neg at hne
    have hins : insert x T ∈ hfin.toFinset.powerset.filter sep := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset (hfin.mem_toFinset.2 hx) hTS, ?_⟩
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha]; exact hne b hb
      · rw [hb]; intro h; exact hne a ha (by simpa using hsymm _ h)
      · exact hTsep a ha b hb hab
    have hc := hmax _ hins
    rw [Finset.card_insert_of_notMem hxT] at hc
    omega
  choose! f hfT hf using hcov
  refine ⟨T, hsub, hTsep, ?_⟩
  have hmaps : Set.MapsTo (fun x => (f x, x - f x)) (B R) ((T : Set G) ×ˢ B 1) :=
    fun x hx => ⟨hfT x hx, hf x hx⟩
  have hinj : Set.InjOn (fun x => (f x, x - f x)) (B R) := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    calc x = f x + (x - f x) := by abel
      _ = f y + (y - f y) := by rw [h2, h1]
      _ = y := by abel
  calc (B R).encard ≤ ((T : Set G) ×ˢ B 1).encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ = T.card * (B 1).encard := by rw [Set.encard_prod, Set.encard_coe_eq_coe_finsetCard]

example : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ R : ℝ, (B R).Finite → ∃ T : Finset G, (T : Set G) ⊆ B R ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → x - y ∉ B 1) ∧ (B R).encard ≤ T.card * (B 1).encard := exists_sep_cover

end GlobalTheory.VolBr
