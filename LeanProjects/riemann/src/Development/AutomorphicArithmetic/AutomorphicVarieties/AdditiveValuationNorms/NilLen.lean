import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

private theorem nilLen_range_succ {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (f : Module.End A M) (k : ℕ) :
    LinearMap.range (f ^ (k + 1)) = (LinearMap.range (f ^ k)).map f := by
  rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]

private theorem nilLen_lt {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (f : Module.End A M) (hf : IsNilpotent f) (k : ℕ) (hk : f ^ k ≠ 0) :
    LinearMap.range (f ^ (k + 1)) < LinearMap.range (f ^ k) := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [pow_succ, Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  · intro h
    apply hk
    obtain ⟨n, hn⟩ := hf
    have key : ∀ j, LinearMap.range (f ^ (k + j)) = LinearMap.range (f ^ k) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [← add_assoc, nilLen_range_succ, ih, ← nilLen_range_succ, h]
    have hkn := key n
    rw [pow_add, hn, mul_zero, LinearMap.range_zero] at hkn
    exact LinearMap.range_eq_bot.mp hkn.symm

theorem UpperTheory.V.PropA.nilLen :
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (f : Module.End A M) (n : ℕ), IsNilpotent f →
      Module.length A M ≤ n → f ^ n = 0 := by
  intro A M _ _ _ f n hf hlen
  by_contra hne
  have hm : ∀ m, m ≤ n → f ^ m ≠ 0 := fun m hm h0 => hne (pow_eq_zero_of_le hm h0)
  have key : ∀ j m, m + j = n → (j : ℕ∞) + 1 ≤ Order.height (LinearMap.range (f ^ m)) := by
    intro j
    induction j with
    | zero =>
      intro m hmj
      have hlt : (⊥ : Submodule A M) < LinearMap.range (f ^ m) := by
        rw [bot_lt_iff_ne_bot, Ne, LinearMap.range_eq_bot]
        exact hm m (by omega)
      have h0 := Order.height_add_one_le hlt
      simp only [Nat.cast_zero, zero_add]
      exact le_trans le_add_self h0
    | succ j ih =>
      intro m hmj
      have h1 := ih (m + 1) (by omega)
      have h2 := Order.height_add_one_le (nilLen_lt f hf m (hm m (by omega)))
      calc ((j + 1 : ℕ) : ℕ∞) + 1 = ((j : ℕ∞) + 1) + 1 := by push_cast; rfl
        _ ≤ Order.height (LinearMap.range (f ^ (m + 1))) + 1 := by gcongr
        _ ≤ _ := h2
  have h3 := key n 0 (by omega)
  rw [Module.length_eq_height] at hlen
  have h4 : Order.height (LinearMap.range (f ^ 0)) ≤ Order.height (⊤ : Submodule A M) :=
    Order.height_mono le_top
  have h5 : ((n : ℕ) : ℕ∞) + 1 ≤ (n : ℕ∞) := h3.trans (h4.trans hlen)
  norm_cast at h5
  omega
