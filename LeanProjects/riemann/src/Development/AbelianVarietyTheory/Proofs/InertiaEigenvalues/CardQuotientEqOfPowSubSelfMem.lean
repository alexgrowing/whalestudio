import Mathlib
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem card_quotient_eq_of_pow_sub_self_mem : ∀ {R : Type} [CommRing R] (P : Ideal R) [P.IsMaximal] (q : ℕ) (ζ : R), 2 ≤ q → ζ ^ (q - 1) = 1 →
    (∀ j : ℕ, 0 < j → j < q - 1 → ζ ^ j - 1 ∉ P) → (∀ y : R, y ^ q - y ∈ P) → Nat.card (R ⧸ P) = q := by
  intro R _ P _ q ζ hq hζ hprim hall
  classical
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hfix : ∀ x : R ⧸ P, x ^ q = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hall y
  set f : Polynomial (R ⧸ P) := X ^ q - X with hf
  have hdeg : f.natDegree = q := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega
  have hf0 : f ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; omega
  have hmem : ∀ x : R ⧸ P, x ∈ f.roots.toFinset := by
    intro x
    rw [Multiset.mem_toFinset, mem_roots hf0]
    simp [hf, hfix x]
  haveI : Finite (R ⧸ P) := by
    apply Finite.of_injective (fun x : R ⧸ P => (⟨x, hmem x⟩ : f.roots.toFinset))
    intro a b h; simpa using congrArg Subtype.val h
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    calc Fintype.card (R ⧸ P) = (Finset.univ : Finset (R ⧸ P)).card := rfl
      _ ≤ f.roots.toFinset.card := Finset.card_le_card (fun x _ => hmem x)
      _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := card_roots' f
      _ = q := hdeg
  · set z : R ⧸ P := Ideal.Quotient.mk P ζ with hz
    have hz1 : z ^ (q - 1) = 1 := by rw [hz, ← map_pow, hζ, map_one]
    have hz0 : z ≠ 0 := by
      intro h; rw [h, zero_pow (by omega)] at hz1; exact zero_ne_one hz1
    have hord : orderOf z = q - 1 := by
      rw [orderOf_eq_iff (by omega)]
      refine ⟨hz1, fun m hm hm0 h => hprim m hm0 hm ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, ← hz, h, sub_self]
    have hinj := pow_injOn_Iio_orderOf (x := z)
    rw [hord] at hinj
    let g : Fin q → R ⧸ P := fun i => if (i : ℕ) = 0 then 0 else z ^ ((i : ℕ) - 1)
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g] at hab
      apply Fin.ext
      by_cases ha : (a : ℕ) = 0 <;> by_cases hb : (b : ℕ) = 0 <;> simp only [ha, hb, if_true, if_false] at hab
      · omega
      · exact absurd hab.symm (pow_ne_zero _ hz0)
      · exact absurd hab (pow_ne_zero _ hz0)
      · have := hinj (show (a : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega)
          (show (b : ℕ) - 1 ∈ Set.Iio (q - 1) by simp; omega) hab
        omega
    have := Nat.card_le_card_of_injective g hg
    simpa using this

end GlobalTheory
