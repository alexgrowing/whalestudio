import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem multinomial_val (p : ℕ) {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (Nat.multinomial s f).factorization p ≤ (s.card - 1) * Nat.log p (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha,
      Nat.add_sub_cancel]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have h1 := @Nat.factorization_choose_le_log p (f a + ∑ i ∈ s, f i) (f a)
      have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
        Nat.log_mono_right (Nat.le_add_left _ _)
      obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, (Nat.succ_pred_eq_of_pos hs.card_pos).symm⟩
      rw [hk, Nat.add_sub_cancel] at ih
      rw [hk, add_mul, one_mul]
      have h3 := ih.trans (Nat.mul_le_mul_left k h2)
      omega

theorem natCast_unit {O : Type*} [CommRing O] [IsLocalRing O] {p : ℕ} (hpO : ¬ IsUnit (p : O)) {n : ℕ}
    (hn : Nat.Coprime n p) : IsUnit (n : O) := by
  by_contra hn'
  have hm : (n : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hn'
  have hp : (p : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hpO
  have h := Nat.gcd_eq_gcd_ab n p
  rw [hn, Nat.cast_one] at h
  have h' : (1 : O) = (n : O) * (Nat.gcdA n p : O) + (p : O) * (Nat.gcdB n p : O) := by
    have := congrArg (Int.cast : ℤ → O) h
    push_cast at this
    exact this
  have hone : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [h']
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hp)
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal O).ne_top hone

theorem pow_div_int {O K : Type*} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] {p : ℕ} (hp : p.Prime)
    (hpO : ¬ IsUnit (p : O)) (hK : (p : K) ≠ 0) {M E : ℕ} (hM : M ≠ 0) (hE : M.factorization p ≤ E) :
    ∃ y : O, (p : K) ^ E / (M : K) = algebraMap O K y := by
  obtain ⟨u, hu⟩ := natCast_unit hpO (n := M / p ^ M.factorization p)
    ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_ordCompl hp hM))))
  refine ⟨(p : O) ^ (E - M.factorization p) * ((u⁻¹ : Oˣ) : O), ?_⟩
  have hMe : (M : K) = (p : K) ^ M.factorization p * algebraMap O K (u : O) := by
    rw [hu, map_natCast, ← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have hu0 : algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hu1 : algebraMap O K (u : O) ≠ 0 := left_ne_zero_of_mul_eq_one hu0
  rw [hMe, map_mul, map_pow, map_natCast, div_eq_iff (mul_ne_zero (pow_ne_zero _ hK) hu1)]
  calc (p : K) ^ E = (p : K) ^ (E - M.factorization p) * (p : K) ^ M.factorization p := by
        rw [← pow_add, Nat.sub_add_cancel hE]
    _ = _ := by
        linear_combination (-(p : K) ^ (E - M.factorization p) * (p : K) ^ M.factorization p) * hu0

theorem expFact_eq {ι : Type*} [Fintype ι] {n : ℕ} (μ : ι × Fin n →₀ ℕ) :
    expFact μ = ∏ x : ι, ∏ c : Fin n, (μ (x, c)).factorial := by
  rw [expFact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]

theorem expFact_mul {ι : Type*} [Fintype ι] {n : ℕ} (p : ℕ) (d : ι → ℕ) (μ : ι × Fin n →₀ ℕ)
    (hμ : ∀ x, multideg μ x = d x) :
    ∃ M : ℕ, M ≠ 0 ∧ expFact μ * M = ∏ x, (d x).factorial ∧
      M.factorization p ≤ ∑ x, (n - 1) * Nat.log p (d x) := by
  classical
  refine ⟨∏ x : ι, Nat.multinomial Finset.univ (fun c : Fin n => μ (x, c)), ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun x _ => (Nat.multinomial_pos _ _).ne'
  · rw [expFact_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Nat.multinomial_spec, ← hμ x]
    rfl
  · rw [Nat.factorization_prod fun x _ => (Nat.multinomial_pos _ _).ne', Finsupp.finset_sum_apply]
    refine Finset.sum_le_sum fun x _ => ?_
    have := multinomial_val p Finset.univ (fun c : Fin n => μ (x, c))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [← hμ x]
    exact this

theorem zTen_expFact {O K : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] {p : ℕ} (hp : p.Prime)
    (hpO : ¬ IsUnit (p : O)) [CharZero K] {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ)
    (μ : (TT × Bool) × Fin (m + 1) →₀ ℕ) (hμ : ∀ x, multideg μ x = hhDegs TT aT bT x) :
    ∃ y : O, zTen K p m TT aT bT * (expFact μ : K) = algebraMap O K y := by
  obtain ⟨M, hM0, hM, hv⟩ := expFact_mul p (hhDegs TT aT bT) μ hμ
  have hE : M.factorization p ≤ kapZ p m TT aT bT := by
    refine hv.trans (Finset.sum_le_sum fun x _ => Nat.mul_le_mul_right _ (by omega))
  obtain ⟨y, hy⟩ := pow_div_int (O := O) (K := K) hp hpO (Nat.cast_ne_zero.2 hp.ne_zero) hM0 hE
  refine ⟨y, ?_⟩
  rw [← hy]
  unfold zTen
  have h1 : (∏ x : TT × Bool, ((hhDegs TT aT bT x).factorial : K)) = (expFact μ : K) * (M : K) := by
    rw [← Nat.cast_mul, hM, Nat.cast_prod]
  have h2 : (expFact μ : K) ≠ 0 := by
    intro h0
    have : (∏ x : TT × Bool, ((hhDegs TT aT bT x).factorial : K)) = 0 := by rw [h1, h0, zero_mul]
    exact (Finset.prod_ne_zero_iff.2 fun x _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)) this
  have h3 : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM0
  rw [h1]
  field_simp

end Formalism.MainNotions.ColumnSystems.Pf
