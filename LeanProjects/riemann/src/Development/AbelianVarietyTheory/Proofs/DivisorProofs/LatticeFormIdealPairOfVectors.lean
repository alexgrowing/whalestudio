import Mathlib
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_coords_of_alt_pair {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0)
    {v w : V} (hv : v ≠ 0) (hw : B w v = 1) (u : V) : ∃ p q : F, p • v + q • w = u := by
  have hli : LinearIndependent F ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : B (s • v + t • w) v = 0 := by rw [h]; simp
    have ht : t = 0 := by simpa [hB, hw] using h1
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero] at h
    exact ⟨h.resolve_right hv, rfl⟩
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hr : Set.range ![v, w] = {v, w} := by
    simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
  rw [hr] at hsp
  have hu : u ∈ Submodule.span F ({v, w} : Set V) := by rw [hsp]; trivial
  exact Submodule.mem_span_pair.mp hu

theorem lattice_eq_ideal_sum_and_mul_eq :
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v w : V}, v ≠ 0 → ∀ (I K : FractionalIdeal (𝓞 F)⁰ F), (∀ a : F, a ∈ I ↔ a • v ∈ L) →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → B w v = 1 → (∀ t ∈ K, t • w ∈ L) →
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J := by
  intro F V _ _ _ _ hV B hB L _ hadd hsmul J hJ hJs v w hv I K hI hK hw hwL
  have hvw : B v w = -1 := by
    have h := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB, hw] at h
    linear_combination h
  have hmem : ∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, q, rfl⟩ := exists_coords_of_alt_pair hV B hB hv hw x
      have hq : q ∈ K := (hK q).2 ⟨_, hx, by simp [hB, hw]⟩
      refine ⟨p, (hI p).2 ?_, q, hq, rfl⟩
      have h1 := hadd _ hx _ (hsmul (-1) _ (hwL q hq))
      simpa using h1
    · rintro ⟨a, ha, t, ht, rfl⟩
      exact hadd _ ((hI a).1 ha) _ (hwL t ht)
  refine ⟨hmem, le_antisymm ?_ ?_⟩
  · rw [FractionalIdeal.mul_le]
    intro a ha t ht
    have h := hJ _ (hwL t ht) _ ((hI a).1 ha)
    simpa [hw, mul_comm] using h
  · intro t ht
    have h := hJs t ht
    have hle : Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}
        ≤ ((I * K : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, z', hz', rfl⟩
      obtain ⟨a, ha, s, hs, rfl⟩ := (hmem z).1 hz
      obtain ⟨a', ha', s', hs', rfl⟩ := (hmem z').1 hz'
      have e : B (a • v + s • w) (a' • v + s' • w) = a' * s - a * s' := by
        simp [hB, hw, hvw]; ring
      rw [e]
      exact Submodule.sub_mem _ (FractionalIdeal.mul_mem_mul ha' hs)
        (FractionalIdeal.mul_mem_mul ha hs')
    exact hle h

end GlobalTheory
