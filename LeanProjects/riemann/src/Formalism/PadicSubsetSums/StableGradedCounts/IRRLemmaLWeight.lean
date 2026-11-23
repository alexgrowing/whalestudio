import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem torus_bounds (g : ℕ) (hg : 2 ≤ g) (d : Multiset ℕ) : (∀ x ∈ d, 1 ≤ x) →
    0 < (d.map (fun x => (g : ℝ) ^ x - 1)).prod ∧
    (d.map (fun x => (g : ℝ) ^ x - 1)).prod ≤ (g : ℝ) ^ d.sum ∧
    (g : ℝ) ^ d.sum * (1 - (d.card : ℝ) / g) ≤ (d.map (fun x => (g : ℝ) ^ x - 1)).prod := by
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  induction d using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
    have hga : (g : ℝ) ≤ (g : ℝ) ^ a :=
      calc (g : ℝ) = (g : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (g : ℝ) ^ a := pow_le_pow_right₀ (by linarith) ha
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons,
      pow_add]
    have hG : 0 < (g : ℝ) ^ s.sum := pow_pos (by linarith) _
    generalize (s.map (fun x => (g : ℝ) ^ x - 1)).prod = T at h1 h2 h3 ⊢
    generalize (g : ℝ) ^ s.sum = G at h2 h3 hG ⊢
    generalize (g : ℝ) ^ a = A at hga ⊢
    have hc : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    push_cast
    generalize (s.card : ℝ) = c at h3 hc ⊢
    refine ⟨mul_pos (by linarith) h1, ?_, ?_⟩
    · calc (A - 1) * T ≤ A * T := by nlinarith [h1]
        _ ≤ A * G := mul_le_mul_of_nonneg_left h2 (by linarith)
    · have hg0 : (g : ℝ) ≠ 0 := by linarith
      have e1 : (A - 1) * (G * (1 - c / g)) - A * G * (1 - (c + 1) / g)
          = G * ((A - g + c) / g) := by
        field_simp; ring
      have e2 : 0 ≤ G * ((A - g + c) / g) :=
        mul_nonneg hG.le (div_nonneg (by linarith) (by linarith))
      calc A * G * (1 - (c + 1) / g) ≤ (A - 1) * (G * (1 - c / g)) := by linarith
        _ ≤ (A - 1) * T := mul_le_mul_of_nonneg_left h3 (by linarith)

theorem lemma_L_weight_holds : LemmaLWeight := by
  intro d g k n hd hg hk hkN hlow hup
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (0 : ℝ) < g := by linarith
  obtain ⟨hT0, hT1, hT2⟩ := torus_bounds g hg d hd
  set T := (d.map (fun x => (g : ℝ) ^ x - 1)).prod with hTdef
  set N := d.sum with hN
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := pow_pos hg0 k
  have hgN : (0 : ℝ) < (g : ℝ) ^ N := pow_pos hg0 N
  have hk1 : (g : ℝ) ^ k = (g : ℝ) ^ (k - 1) * g := by
    rw [← pow_succ]; congr 1; omega
  constructor
  ·
    have h1 : (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) ≤ n := by
      have : (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) = (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) := by
        rw [hk1]; field_simp
      rw [this]; exact hlow
    have h0 : (0 : ℝ) ≤ 1 - 1 / (g : ℝ) := by
      rw [sub_nonneg, div_le_one hg0]; linarith
    rw [div_le_div_iff₀ hgN (mul_pos hgk hT0)]
    calc (1 - 1 / (g : ℝ)) * ((g : ℝ) ^ k * T) = ((g : ℝ) ^ k * (1 - 1 / (g : ℝ))) * T := by ring
      _ ≤ ((g : ℝ) ^ k * (1 - 1 / (g : ℝ))) * (g : ℝ) ^ N :=
          mul_le_mul_of_nonneg_left hT1 (mul_nonneg hgk.le h0)
      _ ≤ n * (g : ℝ) ^ N := mul_le_mul_of_nonneg_right h1 hgN.le
  · intro h2N
    set t : ℝ := (N : ℝ) / g with ht
    have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hg0.le
    have ht1 : t ≤ 1 / 2 := by
      rw [ht, div_le_iff₀ hg0]
      have : (2 : ℝ) * N ≤ g := by exact_mod_cast h2N
      linarith

    have hsum : ∑ i ∈ Finset.range (k + 1), (N : ℝ) ^ i * (g : ℝ) ^ (k - i)
        = (g : ℝ) ^ k * ∑ i ∈ Finset.range (k + 1), t ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have : (g : ℝ) ^ k = (g : ℝ) ^ (k - i) * (g : ℝ) ^ i := by
        rw [← pow_add]; congr 1; omega
      rw [ht, div_pow, this]
      have hgi : (g : ℝ) ^ i ≠ 0 := (pow_pos hg0 i).ne'
      field_simp
    have hgeom : (∑ i ∈ Finset.range (k + 1), t ^ i) * (1 - t) ≤ 1 := by
      rw [geom_sum_mul_neg]
      have : 0 ≤ t ^ (k + 1) := pow_nonneg ht0 _
      linarith
    have hcard : (d.card : ℝ) ≤ (N : ℝ) := by
      have := Multiset.card_nsmul_le_sum hd
      simp only [smul_eq_mul, mul_one] at this
      exact_mod_cast this
    have hT3 : (g : ℝ) ^ N * (1 - t) ≤ T := by
      refine le_trans ?_ hT2
      apply mul_le_mul_of_nonneg_left _ hgN.le
      have : (d.card : ℝ) / g ≤ t := div_le_div_of_nonneg_right hcard hg0.le
      linarith
    have h1t : (0 : ℝ) < 1 - t := by linarith
    set st := ∑ i ∈ Finset.range (k + 1), t ^ i with hsdef
    have hs0 : 0 ≤ st := Finset.sum_nonneg (fun i _ => pow_nonneg ht0 i)
    have hpoly : 1 ≤ (1 + 6 * t) * (1 - t) ^ 2 := by nlinarith [mul_nonneg ht0 (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * t) (by linarith : (0:ℝ) ≤ 4 - 3 * t))]
    have e6 : 1 + 6 * (N : ℝ) / g = 1 + 6 * t := by rw [ht]; ring
    rw [e6, div_le_div_iff₀ (mul_pos hgk hT0) hgN]
    have hn : n ≤ (g : ℝ) ^ k * st := by rw [← hsum]; exact hup

    have hA : st ≤ (1 + 6 * t) * (1 - t) := by
      have h7 : st * (1 - t) ≤ ((1 + 6 * t) * (1 - t)) * (1 - t) := by
        calc st * (1 - t) ≤ 1 := hgeom
          _ ≤ (1 + 6 * t) * (1 - t) ^ 2 := hpoly
          _ = ((1 + 6 * t) * (1 - t)) * (1 - t) := by ring
      exact le_of_mul_le_mul_right h7 h1t
    calc n * (g : ℝ) ^ N ≤ ((g : ℝ) ^ k * st) * (g : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right hn hgN.le
      _ ≤ ((g : ℝ) ^ k * ((1 + 6 * t) * (1 - t))) * (g : ℝ) ^ N := by
          apply mul_le_mul_of_nonneg_right _ hgN.le
          exact mul_le_mul_of_nonneg_left hA hgk.le
      _ = (1 + 6 * t) * ((g : ℝ) ^ k * ((g : ℝ) ^ N * (1 - t))) := by ring
      _ ≤ (1 + 6 * t) * ((g : ℝ) ^ k * T) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hT3 hgk.le

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
