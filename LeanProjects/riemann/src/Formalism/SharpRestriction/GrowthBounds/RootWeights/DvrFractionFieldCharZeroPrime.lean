import Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Arith

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem natCast_unit_of_coprime (S : UniformizedDVR p O) {c : ℕ} (hc : Nat.Coprime c p) : IsUnit (c : O) := by
  by_contra h
  have hc' : (c : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have key : ((c.gcd p : ℕ) : ℤ) = (c : ℤ) * c.gcdA p + (p : ℤ) * c.gcdB p := Nat.gcd_eq_gcd_ab c p
  rw [Nat.Coprime.gcd_eq_one hc, Nat.cast_one] at key
  have key' : (1 : O) = (c : O) * ((c.gcdA p : ℤ) : O) + (p : O) * ((c.gcdB p : ℤ) : O) := by
    have := congrArg (Int.cast : ℤ → O) key
    push_cast at this
    exact this
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [key']
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hc') (Ideal.mul_mem_right _ _ S.p_mem)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem dvr_charZero_of_prime (S : UniformizedDVR p O) (hp : p.Prime) : CharZero O := by
  refine charZero_of_inj_zero (fun n hn => ?_)
  by_contra hne
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hne p hp.ne_one
  rw [Nat.cast_mul, Nat.cast_pow] at hn
  have hpe : (p : O) ^ e ≠ 0 := pow_ne_zero _ S.p_ne
  have hm0 : (m : O) = 0 := (mul_eq_zero.1 hn).resolve_left hpe
  have hu := natCast_unit_of_coprime S ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  rw [hm0] at hu
  exact not_isUnit_zero hu

theorem dvr_fraction_field_charZero_prime (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  haveI := dvr_charZero_of_prime S hp
  refine charZero_of_inj_zero (fun n hn => ?_)
  have h1 : algebraMap O (KK O) (n : O) = algebraMap O (KK O) 0 := by
    rw [map_natCast, map_zero]; exact hn
  have h2 : (n : O) = 0 := IsFractionRing.injective O (KK O) h1
  exact_mod_cast h2

theorem exists_mul_natCast_eq_prime_pow (S : UniformizedDVR p O) (hp : p.Prime) {N de : ℕ} (hN : N ≠ 0) (hv : N.factorization p ≤ de) :
    ∃ o : O, o * (N : O) = (p : O) ^ de := by
  obtain ⟨u, hu⟩ := natCast_unit_of_coprime S (c := N / p ^ N.factorization p)
    (Nat.Coprime.symm (Nat.coprime_ordCompl hp hN))
  refine ⟨(p : O) ^ (de - N.factorization p) * ↑u⁻¹, ?_⟩
  have hN' : (N : O) = (p : O) ^ (N.factorization p) * ((N / p ^ N.factorization p : ℕ) : O) := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self N p]
    rw [Nat.cast_mul, Nat.cast_pow]
  rw [hN', ← hu]
  calc (p : O) ^ (de - N.factorization p) * ↑u⁻¹ * ((p : O) ^ (N.factorization p) * ↑u)
      = (p : O) ^ (de - N.factorization p) * (p : O) ^ (N.factorization p) * (↑u⁻¹ * ↑u) := by ring
    _ = (p : O) ^ de := by rw [Units.inv_mul, mul_one, ← pow_add, Nat.sub_add_cancel hv]

end Arith

section Order

theorem card_ordered_pairs_lt (n : ℕ) : (univ.filter fun ab : Fin n × Fin n => ab.1 < ab.2).card = N0 n := by
  unfold N0
  rw [← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) n]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Fin.card_Iio b]
  refine Finset.card_bij (fun ab _ => ab.1) ?_ ?_ ?_
  · intro ab h
    simp only [mem_filter, mem_univ, true_and] at h
    rw [Finset.mem_Iio, ← h.2]
    exact h.1
  · intro x hx y hy hxy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    exact Prod.ext hxy (hx.2.trans hy.2.symm)
  · intro a ha
    exact ⟨(a, b), by simpa using ha, rfl⟩

theorem normal_order_length_eq {n : ℕ} {ord : List (Fin n × Fin n)} (h : NormalOrder n ord) : ord.length = N0 n := by
  obtain ⟨hnd, hlt, hall, -⟩ := h
  rw [← card_ordered_pairs_lt n, ← List.toFinset_card_of_nodup hnd]
  congr 1
  ext ab
  simp only [List.mem_toFinset, mem_filter, mem_univ, true_and]
  exact ⟨hlt ab, fun h => hall ab.1 ab.2 h⟩

theorem pairwise_list_index_lt {α : Type*} [BEq α] [LawfulBEq α] (r : α → α → Prop) (hasym : ∀ x y, r x y → ¬ r y x)
    (l : List α) (hl : l.Pairwise r) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : r x y) :
    l.idxOf x < l.idxOf y := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.idxOf_cons, beq_iff_eq, cond_eq_if]
    by_cases hax : a = x
    · subst hax
      by_cases hay : a = y
      · subst hay; exact absurd hxy (hasym _ _ hxy)
      · simp [hay]
    · have hxt : x ∈ t := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hax
        · exact h
      by_cases hay : a = y
      · subst hay; exact absurd (hl.1 x hxt) (hasym _ _ hxy)
      · have hyt : y ∈ t := by
          rcases List.mem_cons.1 hy with h | h
          · exact absurd h.symm hay
          · exact h
        have := ih hl.2 hxt hyt
        simp [List.idxOf_cons, hax, hay]
        omega

theorem exists_normalOrder (n : ℕ) : ∃ ord, NormalOrder n ord := by
  let R : Fin n × Fin n → Fin n × Fin n → Prop := fun p q => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)
  have hasym : ∀ x y, R x y → ¬ R y x := by
    intro x y h h'
    rcases h with h | ⟨e, h⟩ <;> rcases h' with h' | ⟨e', h'⟩
    · exact lt_asymm h h'
    · rw [e'] at h; exact lt_irrefl _ h
    · rw [e] at h'; exact lt_irrefl _ h'
    · exact lt_asymm h h'
  let L : List (Fin n × Fin n) := (List.finRange n).flatMap
    (fun a => ((List.finRange n).filter (fun b => decide (a < b))).map (fun b => (a, b)))
  have hmem : ∀ ab : Fin n × Fin n, ab ∈ L ↔ ab.1 < ab.2 := by
    rintro ⟨a, b⟩
    simp [L]
  have hpw : L.Pairwise R := by
    simp only [L, List.pairwise_flatMap]
    refine ⟨fun a _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      refine List.Pairwise.imp (fun {b c} h => Or.inr ⟨rfl, h⟩) ?_
      exact (List.pairwise_lt_finRange n).filter _
    · refine List.Pairwise.imp (fun {a₁ a₂} h => ?_) (List.pairwise_lt_finRange n)
      intro x hx y hy
      simp only [List.mem_map] at hx hy
      obtain ⟨b, -, rfl⟩ := hx
      obtain ⟨c, -, rfl⟩ := hy
      exact Or.inl h
  refine ⟨L, ?_, fun ab h => (hmem ab).1 h, fun a b h => (hmem (a, b)).2 h, ?_⟩
  · exact hpw.imp (fun {x y} h e => by subst e; exact hasym x x h h)
  · intro a b c hab hbc
    left
    constructor
    · exact pairwise_list_index_lt R hasym L hpw ((hmem _).2 hab) ((hmem _).2 (lt_trans hab hbc)) (Or.inr ⟨rfl, hbc⟩)
    · exact pairwise_list_index_lt R hasym L hpw ((hmem _).2 (lt_trans hab hbc)) ((hmem _).2 hbc) (Or.inl hab)

end Order

end Formalism.MainNotions.G.GLWeightTheory
