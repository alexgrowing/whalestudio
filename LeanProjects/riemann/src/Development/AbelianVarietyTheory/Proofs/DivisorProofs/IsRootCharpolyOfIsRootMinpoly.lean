import Mathlib

open Polynomial

namespace GlobalTheory.SumScalarVanishing

section
variable {F C E : Type} [Field F] [Ring C] [Algebra F C] [Field E] [Algebra F E]

theorem eq_zero_of_sum_smul [Algebra.IsCentral F C] [IsSimpleRing C] {n : ℕ} (hn : 0 < n)
    (ρ : C →+* Matrix (Fin n) (Fin n) E)
    (hρ : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (algebraMap F E a))
    {ι : Type} (e : ι → E) (he : LinearIndependent F e) (s : Finset ι) :
    ∀ c : ι → C, ∑ i ∈ s, e i • ρ (c i) = 0 → ∀ i ∈ s, c i = 0 := by
  classical
  have hmain : ∀ (k : ℕ) (c : ι → C), (s.filter (fun i => c i ≠ 0)).card = k →
      ∑ i ∈ s, e i • ρ (c i) = 0 → ∀ i ∈ s, c i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro c hk hsum i0 hi0
    by_contra hci0

    let I : TwoSidedIdeal C := TwoSidedIdeal.mk'
      {a | ∃ d : ι → C, d i0 = a ∧ (∀ i ∈ s, c i = 0 → d i = 0) ∧ ∑ i ∈ s, e i • ρ (d i) = 0}
      ⟨0, rfl, fun _ _ _ => rfl, by simp⟩
      (by
        rintro x y ⟨d, rfl, hd, hds⟩ ⟨d', rfl, hd', hds'⟩
        refine ⟨d + d', rfl, fun i hi hc => by simp [hd i hi hc, hd' i hi hc], ?_⟩
        simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib, hds, hds', add_zero])
      (by
        rintro x ⟨d, rfl, hd, hds⟩
        refine ⟨-d, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [Pi.neg_apply, map_neg, smul_neg, Finset.sum_neg_distrib, hds, neg_zero])
      (by
        rintro x y ⟨d, rfl, hd, hds⟩
        refine ⟨fun i => x * d i, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [map_mul, ← Matrix.mul_smul, ← Finset.mul_sum, hds, mul_zero])
      (by
        rintro x y ⟨d, rfl, hd, hds⟩
        refine ⟨fun i => d i * y, rfl, fun i hi hc => by simp [hd i hi hc], ?_⟩
        simp only [map_mul, ← Matrix.smul_mul, ← Finset.sum_mul, hds, zero_mul])
    have hmem : ∀ a, a ∈ I ↔
        ∃ d : ι → C, d i0 = a ∧ (∀ i ∈ s, c i = 0 → d i = 0) ∧ ∑ i ∈ s, e i • ρ (d i) = 0 :=
      fun a => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a
    have hI : I = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top I with h | h
      · exfalso
        have h' : c i0 ∈ I := (hmem _).2 ⟨c, rfl, fun i _ hc => hc, hsum⟩
        rw [h, TwoSidedIdeal.mem_bot] at h'
        exact hci0 h'
      · exact h
    have h1 : (1 : C) ∈ I := by rw [hI]; trivial
    obtain ⟨d, hd0, hdc, hds⟩ := (hmem 1).1 h1

    have hcen : ∀ i ∈ s, ∀ y : C, y * d i = d i * y := by
      intro i hi y
      let d' : ι → C := fun j => y * d j - d j * y
      have hs' : ∑ j ∈ s, e j • ρ (d' j) = 0 := by
        have hsplit : ∑ j ∈ s, e j • ρ (d' j) =
            ρ y * (∑ j ∈ s, e j • ρ (d j)) - (∑ j ∈ s, e j • ρ (d j)) * ρ y := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [d', map_sub, map_mul, smul_sub, Matrix.mul_smul, Matrix.smul_mul]
        rw [hsplit, hds, mul_zero, zero_mul, sub_zero]
      have hsub : s.filter (fun j => d' j ≠ 0) ⊂ s.filter (fun j => c j ≠ 0) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i0, Finset.mem_filter.2 ⟨hi0, hci0⟩, fun h => ?_⟩
          exact (Finset.mem_filter.1 h).2 (by simp [d', hd0])
        · intro j hj
          rw [Finset.mem_filter] at hj ⊢
          refine ⟨hj.1, fun hc => hj.2 ?_⟩
          simp [d', hdc j hj.1 hc]
      have hlt := Finset.card_lt_card hsub
      rw [hk] at hlt
      have := ih _ hlt d' rfl hs' i hi
      exact sub_eq_zero.1 this
    have hex : ∀ i, ∃ a : F, i ∈ s → algebraMap F C a = d i := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨a, ha⟩ := Algebra.mem_bot.1
          (Algebra.IsCentral.out ((Subalgebra.mem_center_iff (R := F)).2 (hcen i hi)))
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose f hf using hex
    have hsum2 : ∑ i ∈ s, f i • e i = 0 := by
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) E => M ⟨0, hn⟩ ⟨0, hn⟩) hds
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← hf i hi, hρ]
      simp [Algebra.smul_def, mul_comm]
    have hf0 := linearIndependent_iff'.1 he s f hsum2 i0 hi0
    have := hf i0 hi0
    rw [hf0, map_zero, hd0] at this
    exact zero_ne_one this
  exact fun c hc => hmain _ c rfl hc

theorem exists_expansion {ι : Type} (b : Module.Basis ι F E) (p : E[X]) :
    ∃ q : ι →₀ F[X], p = q.sum (fun k r => b k • r.map (algebraMap F E)) := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨u, rfl⟩ := hp
    obtain ⟨v, rfl⟩ := hq
    refine ⟨u + v, ?_⟩
    rw [Finsupp.sum_add_index']
    · intro k
      simp
    · intro k r r'
      rw [Polynomial.map_add, smul_add]
  | monomial j a =>
    refine ⟨(b.repr a).mapRange (fun c => Polynomial.monomial j c) (by simp), ?_⟩
    rw [Finsupp.sum_mapRange_index (by simp)]
    simp only [Polynomial.map_monomial, Polynomial.smul_monomial]
    rw [← map_finsuppSum (Polynomial.monomial j)]
    congr 1
    conv_lhs => rw [← b.linearCombination_repr a]
    rw [Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [smul_eq_mul, Algebra.smul_def, mul_comm]

end

theorem isRoot_charpoly_of_isRoot_minpoly {F C E : Type} [Field F] [Ring C] [Algebra F C]
    [FiniteDimensional F C] [Algebra.IsCentral F C] [IsSimpleRing C] [Field E] (τ : F →+* E)
    {n : ℕ} (hn : 0 < n) (ρ : C →+* Matrix (Fin n) (Fin n) E)
    (hρ : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (τ a)) (x : C) (μ : E)
    (hμ : ((minpoly F x).map τ).IsRoot μ) : (ρ x).charpoly.IsRoot μ := by
  classical
  let _ : Algebra F E := τ.toAlgebra
  have hρ' : ∀ a : F, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (algebraMap F E a) := hρ
  let b := Module.Basis.ofVectorSpace F E
  obtain ⟨q, hq⟩ := exists_expansion b (ρ x).charpoly

  have heval : ∀ r : F[X],
      Polynomial.aeval (ρ x) (r.map (algebraMap F E)) = ρ (Polynomial.aeval x r) := by
    intro r
    induction r using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
    | monomial j a =>
      simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, map_mul, map_pow, hρ']
      congr 1

  have h0 : ∑ k ∈ q.support, b k • ρ (Polynomial.aeval x (q k)) = 0 := by
    have h := Matrix.aeval_self_charpoly (ρ x)
    rw [hq, Finsupp.sum, map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, heval]
  have hz := eq_zero_of_sum_smul hn ρ hρ' b b.linearIndependent q.support
    (fun k => Polynomial.aeval x (q k)) h0
  have hdvd : (minpoly F x).map (algebraMap F E) ∣ (ρ x).charpoly := by
    rw [hq, Finsupp.sum]
    refine Finset.dvd_sum fun k hk => ?_
    rw [Polynomial.smul_eq_C_mul]
    exact Dvd.dvd.mul_left (Polynomial.map_dvd _ (minpoly.dvd F x (hz k hk))) _
  exact Polynomial.IsRoot.dvd hμ hdvd

end GlobalTheory.SumScalarVanishing
