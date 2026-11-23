import Mathlib

namespace GlobalTheory.NormResidue

open Polynomial

theorem exists_mul_involution_eq_neg_one {k : Type*} [Field k] [Finite k] (σ : k →+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (h2 : (2 : k) ≠ 0) :
    ∃ z : k, z * σ z + 1 = 0 := by
  classical
  obtain ⟨x, hx⟩ := hne
  let F : Subfield k := σ.eqLocusField (RingHom.id k)
  let _ : Fintype F := Fintype.ofFinite F
  have memF : ∀ y : k, y ∈ F ↔ σ y = y := fun y => Iff.rfl
  have hθ : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ]; ring
  have hθ0 : x - σ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  let d : F := ⟨(x - σ x) * (x - σ x), (memF _).2 (by rw [map_mul, hθ]; ring)⟩
  have hd0 : d ≠ 0 := by
    intro h
    have h' : (x - σ x) * (x - σ x) = 0 := congrArg Subtype.val h
    exact hθ0 (mul_self_eq_zero.mp h')
  have hchar : ringChar F ≠ 2 := by
    intro hc
    apply h2
    have h0 : ((2 : ℕ) : F) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    have h0' := congrArg F.subtype h0
    rwa [map_natCast, map_zero, Nat.cast_ofNat] at h0'
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2 + Polynomial.C 1) (g := Polynomial.C (-d) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_add_C (by norm_num) _)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd0))
    (FiniteField.odd_card_of_char_ne_two hchar)
  have hab' := congrArg Subtype.val hab
  simp [d] at hab'
  have ha : σ a = a := (memF _).1 a.2
  have hb : σ b = b := (memF _).1 b.2
  refine ⟨a + b * (x - σ x), ?_⟩
  rw [map_add, map_mul, ha, hb, hθ]
  linear_combination hab'

theorem exists_mul_involution_add_one_mem_pow (O : Type) [CommRing O] (s : O →+* O)
    (hs : ∀ x, s (s x) = x) (P : Ideal O) [hP : P.IsMaximal] [Finite (O ⧸ P)]
    (hsP : ∀ x ∈ P, s x ∈ P) (hne : ∃ x, s x - x ∉ P) (h2 : (2 : O) ∉ P) (N : ℕ) (z0 : O)
    (hz : N = 0 ∨ z0 * s z0 + 1 ∈ P ^ N) :
    ∃ z : O, z * s z + 1 ∈ P ^ (N + 1) ∧ (N ≠ 0 → z - z0 ∈ P ^ N) := by
  classical
  have hPP : P ≤ P.comap s := fun x hx => hsP x hx
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    letI : Field (O ⧸ P) := Ideal.Quotient.field P
    let σ := Ideal.quotientMap P s hPP
    have hσ : ∀ x, σ (σ x) = x := by
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [σ, Ideal.quotientMap_mk, hs]
    have hne' : ∃ x, σ x ≠ x := by
      obtain ⟨x, hx⟩ := hne
      refine ⟨Ideal.Quotient.mk P x, fun h => hx ?_⟩
      rw [← Ideal.Quotient.eq]
      simpa only [σ, Ideal.quotientMap_mk] using h
    have h2' : (2 : O ⧸ P) ≠ 0 := by
      intro h
      apply h2
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
      exact h
    obtain ⟨w, hw⟩ := exists_mul_involution_eq_neg_one (k := O ⧸ P) σ hσ hne' h2'
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨z, ?_, fun h => absurd rfl h⟩
    rw [zero_add, pow_one, ← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [σ, Ideal.quotientMap_mk, map_add, map_mul, map_one] using hw
  · have hN0 : N ≠ 0 := hN.ne'
    obtain ⟨e, he_def⟩ : ∃ e, e = z0 * s z0 + 1 := ⟨_, rfl⟩
    have he : e ∈ P ^ N := he_def ▸ hz.resolve_left hN0
    have heP : e ∈ P := Ideal.pow_le_self hN0 he
    obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv h2
    have hh : y + s y - 1 ∈ P := by
      have h1 : y * 2 - 1 ∈ P := by
        have h1e : y * 2 - 1 = -i := by linear_combination hyi
        rw [h1e]
        exact P.neg_mem hi
      have h1' : s y * 2 - 1 ∈ P := by
        have h1s := hsP _ h1
        simpa [map_sub, map_mul, map_ofNat] using h1s
      have h3 : 2 * (y + s y - 1) ∈ P := by
        have h3e : 2 * (y + s y - 1) = (y * 2 - 1) + (s y * 2 - 1) := by ring
        rw [h3e]
        exact P.add_mem h1 h1'
      rcases (Ideal.IsMaximal.isPrime hP).mem_or_mem h3 with h | h
      · exact absurd h h2
      · exact h
    refine ⟨z0 + y * z0 * e, ?_, fun _ => ?_⟩
    · have hse : s e = e := by rw [he_def, map_add, map_mul, hs, map_one]; ring
      have key : (z0 + y * z0 * e) * s (z0 + y * z0 * e) + 1
          = e * (1 - (y + s y) + (y + s y) * e) + e * (e * (y * z0 * s y * s z0)) := by
        rw [map_add, map_mul, map_mul, hse]
        rw [he_def]
        ring
      rw [key, pow_succ]
      refine Ideal.add_mem _ (Ideal.mul_mem_mul he ?_)
        (Ideal.mul_mem_mul he (Ideal.mul_mem_right _ _ heP))
      have hx : 1 - (y + s y) + (y + s y) * e = -(y + s y - 1) + (y + s y) * e := by ring
      rw [hx]
      exact P.add_mem (P.neg_mem hh) (Ideal.mul_mem_left _ _ heP)
    · have hx : z0 + y * z0 * e - z0 = y * z0 * e := by ring
      rw [hx]
      exact Ideal.mul_mem_left _ _ he

end GlobalTheory.NormResidue
