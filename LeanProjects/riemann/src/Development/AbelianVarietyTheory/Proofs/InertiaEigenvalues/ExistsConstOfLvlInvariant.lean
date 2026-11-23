import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX

noncomputable section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.LvlInv

theorem aeval_eq_zero_of_complex {N : ℕ} (hN : 0 < N) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N)
    {R : Type} [CommRing R] {t : R} (ht : Polynomial.aeval t (Polynomial.cyclotomic N ℤ) = 0)
    (f : Polynomial ℤ) (hf : Polynomial.aeval ζ f = 0) : Polynomial.aeval t f = 0 := by
  have h := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hN) hf
  rw [← Polynomial.cyclotomic_eq_minpoly hζ hN] at h
  obtain ⟨q, rfl⟩ := h
  rw [map_mul, ht, zero_mul]

theorem exists_geom_int {w : ℂ} {n : ℕ} (h : w ^ n = 1) :
    ∃ c : ℤ, ∑ a ∈ Finset.range n, w ^ a = c := by
  by_cases hw : w = 1
  · exact ⟨n, by simp [hw]⟩
  · refine ⟨0, ?_⟩
    have := geom_sum_mul w n
    rw [h, sub_self] at this
    simpa using (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hw)

theorem exists_sum_int {l k : ℕ} (hl : 0 < l) {w : ℂ} (h : w ^ l ^ (k + 1) = 1) :
    ∃ c : ℤ, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), w ^ a = c := by
  obtain ⟨c, hc⟩ := exists_geom_int h
  obtain ⟨d, hd⟩ := exists_geom_int (w := w ^ l) (n := l ^ k) (by rw [← pow_mul, ← pow_succ', h])
  refine ⟨c - d, ?_⟩
  have e := Finset.sum_filter_add_sum_filter_not (Finset.range (l ^ (k + 1))) (fun a => l ∣ a)
    (fun a => w ^ a)
  have e2 : ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => l ∣ a), w ^ a =
      ∑ a ∈ Finset.range (l ^ k), (w ^ l) ^ a := by
    symm
    refine Finset.sum_bij (fun a _ => l * a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_range, Finset.mem_filter] at ha ⊢
      exact ⟨by rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_left ha hl, dvd_mul_right _ _⟩
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hl hab
    · intro b hb
      simp only [Finset.mem_range, Finset.mem_filter] at hb
      obtain ⟨h1, a, rfl⟩ := hb
      refine ⟨a, ?_, rfl⟩
      rw [pow_succ'] at h1
      exact Finset.mem_range.2 (Nat.lt_of_mul_lt_mul_left h1)
    · intro a _
      rw [pow_mul]
  rw [e2, hc, hd] at e
  push_cast
  linear_combination e

theorem aeval_cyc {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] (t : R) :
    Polynomial.aeval t (Polynomial.cyclotomic (l ^ (k + 1)) ℤ) =
      ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl]
  simp

theorem root_pow {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] {t : R}
    (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) {a : ℕ} (ha : ¬ l ∣ a) :
    ∑ i ∈ Finset.range l, ((t ^ a) ^ l ^ k) ^ i = 0 := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.pos _
  have hζ := Complex.isPrimitiveRoot_exp _ hN.ne'
  rw [← aeval_cyc hl] at ht ⊢
  have h := aeval_eq_zero_of_complex hN hζ ht
    ((Polynomial.cyclotomic (l ^ (k + 1)) ℤ).comp (Polynomial.X ^ a)) (by
      have h2 := hζ.pow_of_coprime a
        (Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hl).2 ha).symm)
      have h3 := h2.isRoot_cyclotomic hN
      rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact h3)
  rwa [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X] at h

theorem sum_pow_int {l : ℕ} (hl : l.Prime) (k : ℕ) {R : Type} [CommRing R] {t : R}
    (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) (j : ℕ) :
    ∃ c : ℤ, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), (t ^ a) ^ j = c := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.pos _
  have hζ := Complex.isPrimitiveRoot_exp _ hN.ne'
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (l ^ (k + 1) : ℕ))
  obtain ⟨c, hc⟩ := exists_sum_int (k := k) hl.pos (w := ζ ^ j)
    (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  rw [← aeval_cyc hl] at ht
  have h := aeval_eq_zero_of_complex hN hζ ht
    (∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a), (Polynomial.X ^ j) ^ a
      - (c : Polynomial ℤ)) (by
      simp only [map_sub, map_sum, map_pow, Polynomial.aeval_X, map_intCast, hc, sub_self])
  simp only [map_sub, map_sum, map_pow, Polynomial.aeval_X, map_intCast, sub_eq_zero] at h
  refine ⟨c, ?_⟩
  rw [← h]
  exact Finset.sum_congr rfl fun a _ => by rw [← pow_mul, ← pow_mul, mul_comm]

theorem sum_aeval_const {l : ℕ} (hl : l.Prime) (k : ℕ) {O R : Type} [CommRing O] [CommRing R]
    [Algebra O R] {t : R} (ht : ∑ i ∈ Finset.range l, (t ^ l ^ k) ^ i = 0) (s : Polynomial O) :
    ∃ c : O, ∑ a ∈ (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a),
      Polynomial.aeval (t ^ a) s = algebraMap O R c := by
  induction s using Polynomial.induction_on' with
  | add r s hr hs =>
    obtain ⟨c, hc⟩ := hr
    obtain ⟨d, hd⟩ := hs
    exact ⟨c + d, by simp only [map_add, Finset.sum_add_distrib, hc, hd]⟩
  | monomial j x =>
    obtain ⟨c, hc⟩ := sum_pow_int hl k ht j
    refine ⟨x * c, ?_⟩
    simp only [Polynomial.aeval_monomial, ← Finset.mul_sum, hc, map_mul, map_intCast]

def lvlPoly (l : ℕ) (O : Type) [CommRing O] (k : ℕ) : Polynomial O :=
  ∑ i ∈ Finset.range l, ((1 + Polynomial.X : Polynomial O) ^ l ^ k) ^ i

theorem coe_lvlPoly (l : ℕ) (O : Type) [CommRing O] (k : ℕ) :
    ((lvlPoly l O k : Polynomial O) : O⟦X⟧) = lvl l O k := by
  have := map_sum (Polynomial.coeToPowerSeries.ringHom (R := O))
    (fun i => ((1 + Polynomial.X : Polynomial O) ^ l ^ k) ^ i) (Finset.range l)
  simp only [map_pow, map_add, map_one, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X] at this
  exact this

theorem algHom_lvl (l : ℕ) {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (k : ℕ)
    (f : O⟦X⟧ →ₐ[O] R) : f (lvl l O k) = ∑ i ∈ Finset.range l, (f (1 + X) ^ l ^ k) ^ i := by
  simp only [lvl, map_sum, map_pow]

theorem lvlPoly_monic {l : ℕ} (hl : l.Prime) (O : Type) [CommRing O] [Nontrivial O] (k : ℕ) :
    (lvlPoly l O k).Monic := by
  have : lvlPoly l O k =
      (Polynomial.cyclotomic (l ^ (k + 1)) O).comp (Polynomial.X + Polynomial.C 1) := by
    rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl, lvlPoly]
    simp [Polynomial.sum_comp, add_comm]
  rw [this]
  exact (Polynomial.cyclotomic.monic _ _).comp_X_add_C _

theorem lvlPoly_map (l : ℕ) {O F : Type} [CommRing O] [CommRing F] (j : O →+* F) (k : ℕ) :
    (lvlPoly l O k).map j = lvlPoly l F k := by
  simp [lvlPoly, Polynomial.map_sum]

theorem lvlPoly_of_char {l : ℕ} [Fact l.Prime] {F : Type} [CommRing F] [IsDomain F]
    (h : (l : F) = 0) (k : ℕ) : lvlPoly l F k = Polynomial.X ^ (l ^ k * (l - 1)) := by
  have hl : l.Prime := Fact.out
  haveI : CharP F l := (CharP.charP_iff_prime_eq_zero hl).2 h
  have e := geom_sum_mul ((1 + Polynomial.X : Polynomial F) ^ l ^ k) l
  rw [← pow_mul, ← pow_succ] at e
  change lvlPoly l F k * _ = _ at e
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, one_pow, add_sub_cancel_left,
    add_sub_cancel_left] at e
  apply mul_right_cancel₀ (pow_ne_zero (l ^ k) Polynomial.X_ne_zero)
  rw [e, ← pow_add]
  congr 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne_zero
  simp [pow_succ, mul_add]

theorem lvlPoly_distinguished {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    (h : ¬ IsUnit (l : O)) (k : ℕ) :
    (lvlPoly l O k).IsDistinguishedAt (IsLocalRing.maximalIdeal O) := by
  have hm := lvlPoly_monic (l := l) Fact.out O k
  refine ⟨⟨fun {n} hn => ?_⟩, hm⟩
  have h0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact h
  have h1 := lvlPoly_map l (IsLocalRing.residue O) k
  rw [lvlPoly_of_char h0] at h1
  have h2 := hm.natDegree_map (IsLocalRing.residue O)
  rw [h1, Polynomial.natDegree_X_pow] at h2
  have h3 := congrArg (fun p => Polynomial.coeff p n) h1
  rw [← h2] at hn
  simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hn.ne, if_false] at h3
  exact (IsLocalRing.residue_eq_zero_iff _).1 h3

end GlobalTheory.CycFr.LvlInv

namespace GlobalTheory.CycFr

open LvlInv

theorem exists_const_of_lvl_invariant {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O]
    [Algebra ℤ_[l] O] (hu : ¬ IsUnit (l : O)) (k : ℕ) (b : O⟦X⟧)
    (hb : ∀ a : ℕ, ¬ l ∣ a → lvl l O k ∣ act O (a : ℤ_[l]) b - b) :
    ∃ c : O, lvl l O k ∣ b - C c := by
  have hl : l.Prime := Fact.out
  have H := lvlPoly_distinguished hu k
  set π := Ideal.Quotient.mkₐ O (Ideal.span {lvl l O k}) with hπ
  have hz : ∀ x, π x = 0 ↔ lvl l O k ∣ x := fun x => by
    rw [hπ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have ht : ∑ i ∈ Finset.range l, ((π (1 + X)) ^ l ^ k) ^ i = 0 := by
    rw [← algHom_lvl]
    exact (hz _).2 dvd_rfl
  obtain ⟨r, hr, q, hq⟩ := GlobalTheory.NB.LT.exists_poly_mod H b
  rw [coe_lvlPoly] at hq
  have hbr : b = r + lvl l O k * q := by rw [← hq]; ring
  obtain ⟨c, hc⟩ := sum_aeval_const hl k ht (r.comp (Polynomial.X - 1))
  set S := (Finset.range (l ^ (k + 1))).filter (fun a => ¬ l ∣ a) with hS
  have h1 : ∀ a ∈ S, Polynomial.aeval ((π (1 + X)) ^ a) (r.comp (Polynomial.X - 1)) = π r := by
    intro a ha
    have ha' : ¬ l ∣ a := (Finset.mem_filter.1 ha).2
    have e1 : π (act O (a : ℤ_[l]) (lvl l O k)) = 0 := by
      have := root_pow hl k ht ha'
      rw [← AlgHom.comp_apply, algHom_lvl, AlgHom.comp_apply, act_one_add_X, bin_nat, map_pow]
      exact this
    have e2 := (hz _).2 (hb a ha')
    rw [hbr] at e2
    simp only [map_sub, map_add, map_mul, e1, (hz _).2 dvd_rfl, zero_mul, add_zero,
      sub_eq_zero] at e2
    rw [← e2, GlobalTheory.NB.LT.algHom_coe, act_nat_X, ← Polynomial.aeval_algHom_apply,
      Polynomial.aeval_comp]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const] at hc
  have hn : S.card ≠ 0 := Finset.card_ne_zero.2 ⟨1, Finset.mem_filter.2
    ⟨Finset.mem_range.2 (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt), hl.not_dvd_one⟩⟩
  set p := lvlPoly l O k with hp
  have h6 : (p : O⟦X⟧) ∣
      ((Polynomial.C (S.card : O) * r - Polynomial.C c : Polynomial O) : O⟦X⟧) := by
    rw [hp, coe_lvlPoly, ← hz, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_C, map_natCast, map_sub, map_mul, map_natCast, algHom_C, ← hc, nsmul_eq_mul,
      sub_self]
  have h7 := GlobalTheory.NB.LT.poly_dvd_of_dvd H h6
  by_cases h0 : r = 0
  · exact ⟨0, q, by simpa [h0] using hq⟩
  have hpos : 0 < p.degree := (Polynomial.zero_le_degree_iff.2 h0).trans_lt hr
  have hn' : (S.card : O) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h8 : Polynomial.C (S.card : O) * r - Polynomial.C c = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt h7 ?_
    refine (Polynomial.degree_sub_le _ _).trans_lt (max_lt ?_ (Polynomial.degree_C_le.trans_lt hpos))
    rwa [Polynomial.degree_C_mul hn']
  have h9 : r.degree ≤ 0 := by
    rw [← Polynomial.degree_C_mul (p := r) hn', sub_eq_zero.1 h8]
    exact Polynomial.degree_C_le
  refine ⟨r.coeff 0, q, ?_⟩
  rw [Polynomial.eq_C_of_degree_le_zero h9, Polynomial.coe_C] at hq
  exact hq

end GlobalTheory.CycFr
