import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPowSubOneLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.CycTrace
open Polynomial

theorem norm_root_eq_one {K : Type*} [NormedField K] {n : ℕ} (hn : n ≠ 0) {ζ : K}
    (hζ : ζ ^ n = 1) : ‖ζ‖ = 1 := by
  have := congrArg norm hζ
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

theorem norm_pow_sub_one_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {ζ : K} (hz : ‖ζ‖ = 1) (a : ℕ) : ‖ζ ^ a - 1‖ ≤ ‖ζ - 1‖ := by
  first
  | exact @_root_.GlobalTheory.NormPowSubOne.main
  | exact _root_.GlobalTheory.NormPowSubOne.main
  | (apply _root_.GlobalTheory.NormPowSubOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormPowSubOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormPowSubOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormPowSubOne.main ..)

theorem norm_sub_one_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (hn : n ≠ 0) {ζ μ : K} (hζ : IsPrimitiveRoot ζ n) (hμ : μ ^ n = 1) :
    ‖μ - 1‖ ≤ ‖ζ - 1‖ := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨a, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  exact norm_pow_sub_one_le (norm_root_eq_one hn hζ.pow_eq_one) a

theorem norm_sub_one_pow_totient {K : Type*} [NormedField K] [IsUltrametricDist K]
    (l : ℕ) [hl : Fact l.Prime] (k : ℕ) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ (k + 1))) :
    ‖ζ - 1‖ ^ (l ^ (k + 1)).totient = ‖(l : K)‖ := by
  have hp := hl.out
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := K) (p := l) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  have h2 := congrArg norm h1
  rw [norm_prod] at h2
  have h3 : ∀ μ ∈ primitiveRoots (l ^ (k + 1)) K,
      ‖Polynomial.eval 1 (Polynomial.X - Polynomial.C μ)‖ = ‖ζ - 1‖ := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).1 hμ
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, norm_sub_rev]
    exact le_antisymm (norm_sub_one_le hn hζ hμ'.pow_eq_one)
      (norm_sub_one_le hn hμ' hζ.pow_eq_one)
  rwa [Finset.prod_congr rfl h3, Finset.prod_const, hζ.card_primitiveRoots] at h2

theorem norm_le_norm_sum {K ι : Type*} [NormedField K] [IsUltrametricDist K] (s : Finset ι)
    (f : ι → K) (h : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → ‖f i‖ = ‖f j‖ → i = j) {i : ι} (hi : i ∈ s) :
    ‖f i‖ ≤ ‖∑ j ∈ s, f j‖ := by
  classical
  obtain ⟨k, hk, hmax⟩ := s.exists_max_image (fun j => ‖f j‖) ⟨i, hi⟩
  refine (hmax i hi).trans ?_
  by_cases h0 : f k = 0
  · simp [h0]
  have hlt : ‖∑ j ∈ s.erase k, f j‖ < ‖f k‖ := by
    rcases (s.erase k).eq_empty_or_nonempty with he | hne
    · simpa [he] using h0
    · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
      refine hle.trans_lt (lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj)) ?_)
      intro e
      exact (Finset.ne_of_mem_erase hj) (h k hk j (Finset.mem_of_mem_erase hj) h0 e.symm).symm
  rw [← Finset.add_sum_erase s f hk, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne']
  exact le_max_left _ _

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_l : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  have h2 : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) l := by simp
  rw [h2, norm_algebraMap', Padic.norm_p]

theorem coeff_bound_unif (π : PadicAlgCl l) (e : ℕ) (hπ : ‖π‖ ^ e = (l : ℝ)⁻¹)
    (Q : ℚ_[l][X]) (hQ : Q.natDegree < e) (k : ℕ) :
    (l : ℝ)⁻¹ * ‖Q.coeff k‖ ≤ ‖aeval π Q‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have he : e ≠ 0 := by omega
  have hr0 : 0 < ‖π‖ := by
    rcases (norm_nonneg π).eq_or_lt with h | h
    · rw [← h, zero_pow he] at hπ
      exact absurd hπ (inv_pos.2 hl0).ne
    · exact h
  have hr1 : ‖π‖ < 1 := by
    by_contra h
    have := one_le_pow₀ (not_lt.1 h) (n := e)
    rw [hπ] at this
    exact absurd (inv_lt_one_of_one_lt₀ hl1) (not_lt.2 this)
  by_cases hk : k < e
  swap
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  rw [aeval_eq_sum_range' hQ]
  refine le_trans ?_ (norm_le_norm_sum (Finset.range e) (fun j => Q.coeff j • π ^ j) ?_
    (Finset.mem_range.2 hk))
  · simp only [norm_smul, norm_pow]
    rw [mul_comm, ← hπ]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hk.le) (norm_nonneg _)
  · intro i hi j hj h0 hij
    simp only [norm_smul, norm_pow] at hij
    have hi0 : Q.coeff i ≠ 0 := fun h => h0 (by simp [h])
    have hj0 : Q.coeff j ≠ 0 := by
      intro h
      rw [h, norm_zero, zero_mul] at hij
      exact (mul_pos (norm_pos_iff.2 hi0) (pow_pos hr0 _)).ne' hij
    rw [Padic.norm_eq_zpow_neg_valuation hi0, Padic.norm_eq_zpow_neg_valuation hj0,
      ← inv_zpow', ← inv_zpow', ← hπ, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne'] at hij
    have h3 := zpow_right_injective₀ hr0 hr1.ne hij
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have h4 : (e : ℤ) ∣ (i : ℤ) - j :=
      ⟨(Q.coeff j).valuation - (Q.coeff i).valuation, by linear_combination h3⟩
    have h5 := Int.eq_zero_of_abs_lt_dvd h4 (by rw [abs_lt]; constructor <;> omega)
    omega

theorem coeff_bound (N : ℕ) (z : PadicAlgCl l) (hz : IsPrimitiveRoot z (l ^ (N + 1)))
    (P : ℚ_[l][X]) (hP : P.natDegree < (l ^ (N + 1)).totient) (k : ℕ) :
    (l : ℝ)⁻¹ * ‖P.coeff k‖ ≤ ‖aeval z P‖ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hπ := norm_sub_one_pow_totient l N z hz
  rw [norm_l] at hπ
  have hQ := coeff_bound_unif (z - 1) _ hπ (taylor 1 P) (by rwa [natDegree_taylor])
  have e1 : aeval (z - 1) (taylor 1 P) = aeval z P := by
    rw [taylor_apply, aeval_comp]; simp
  rw [e1] at hQ
  have e2 : P = taylor (-1) (taylor 1 P) := by rw [taylor_taylor]; simp
  generalize taylor 1 P = Q at hQ e2
  have : ‖P.coeff k‖ ≤ l * ‖aeval z P‖ := by
    conv_lhs => rw [e2, taylor_coeff, eval_eq_sum_range]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
    intro j _
    rw [hasseDeriv_coeff, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    have h1 := IsUltrametricDist.norm_natCast_le_one ℚ_[l] ((j + k).choose k)
    have h2 := hQ (j + k)
    rw [inv_mul_le_iff₀ hl0] at h2
    calc _ ≤ 1 * ‖Q.coeff (j + k)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := by rwa [one_mul]
  rwa [inv_mul_le_iff₀ hl0]

theorem exists_poly (n : ℕ) (hn : 0 < n) (w : PadicAlgCl l) (hw : IsPrimitiveRoot w n)
    (a : PadicAlgCl l) (ha : a ∈ IntermediateField.adjoin ℚ_[l] {w}) :
    ∃ p : ℚ_[l][X], p.natDegree < n.totient ∧ aeval w p = a := by
  have hint : IsIntegral ℚ_[l] w := (hw.isIntegral hn).tower_top
  have h1 : a ∈ (IntermediateField.adjoin ℚ_[l] {w}).toSubalgebra := ha
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at h1
  obtain ⟨q, rfl⟩ := h1
  have hm : (cyclotomic n ℚ_[l]).Monic := cyclotomic.monic n _
  have hroot : aeval w (cyclotomic n ℚ_[l]) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hw.isRoot_cyclotomic hn
  refine ⟨q %ₘ cyclotomic n ℚ_[l], ?_, aeval_modByMonic_eq_self_of_root hroot⟩
  rw [← natDegree_cyclotomic n ℚ_[l]]
  refine natDegree_modByMonic_lt q hm ?_
  intro h
  have := natDegree_cyclotomic n ℚ_[l]
  rw [h, natDegree_one] at this
  exact (Nat.totient_pos.2 hn).ne this

end GlobalTheory.CycTrace

open Polynomial GlobalTheory.CycTrace in

theorem GlobalTheory.CycTrace.normalised_trace_bound (l : ℕ) [hl : Fact l.Prime] (n m : ℕ) (z : Om l)
    (hn : 1 ≤ n) (hz : IsPrimitiveRoot z (l ^ (n + m))) (a : Fin (l ^ m) → Om l)
    (ha : ∀ i, a i ∈ IntermediateField.adjoin ℚ_[l] {z ^ (l ^ m)}) :
    ‖(l : Om l)‖ * ‖a ⟨0, pow_pos (Fact.out : l.Prime).pos m⟩‖ ≤ ‖∑ i, a i * z ^ (i : ℕ)‖ := by
  have hp := hl.out
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hM : 0 < l ^ m := pow_pos hp.pos m
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hw : IsPrimitiveRoot (z ^ (l ^ m)) (l ^ (n + 1)) :=
    hz.pow (pow_pos hp.pos _) (by rw [pow_add, mul_comm])
  choose p hp1 hp2 using fun i => exists_poly _ (pow_pos hp.pos _) _ hw (a i) (ha i)
  have hN : n + 1 + m = (n + m) + 1 := by ring
  rw [hN] at hz
  set P : ℚ_[l][X] := ∑ i : Fin (l ^ m), expand ℚ_[l] (l ^ m) (p i) * X ^ (i : ℕ) with hPdef
  have htot : (l ^ (n + m + 1)).totient = (l ^ (n + 1)).totient * l ^ m := by
    rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]; ring
  have hdeg : P.natDegree < (l ^ (n + m + 1)).totient := by
    have hpos : 0 < (l ^ (n + m + 1)).totient := Nat.totient_pos.2 (pow_pos hp.pos _)
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := (l ^ (n + m + 1)).totient - 1) _ _ ?_) (by omega)
    intro i _
    refine natDegree_mul_le.trans ?_
    rw [natDegree_expand, natDegree_X_pow]
    have h1 := hp1 i
    have h2 := i.2
    have h3 : ((p i).natDegree + 1) * l ^ m ≤ (l ^ (n + 1)).totient * l ^ m :=
      Nat.mul_le_mul_right _ h1
    rw [add_mul] at h3
    omega
  have hev : aeval z P = ∑ i, a i * z ^ (i : ℕ) := by
    rw [hPdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, expand_aeval, hp2]; simp
  have hco : ∀ j, P.coeff (j * l ^ m) = (p ⟨0, hM⟩).coeff j := by
    intro j
    rw [hPdef, finset_sum_coeff, Finset.sum_eq_single ⟨0, hM⟩]
    · simp [coeff_expand_mul hM]
    · intro i _ hi
      rw [coeff_mul_X_pow']
      split_ifs with h
      · rw [coeff_expand hM, if_neg]
        intro hd
        have : l ^ m ∣ (i : ℕ) := by
          have := (Nat.dvd_sub_iff_right h (Dvd.intro_left j rfl)).1 hd
          exact this
        exact hi (Fin.ext (Nat.eq_zero_of_dvd_of_lt this i.2))
      · rfl
    · simp
  have hb := fun j => coeff_bound (n + m) z hz P hdeg (j * l ^ m)
  simp only [hco, hev] at hb
  have hw1 : ‖z ^ (l ^ m)‖ = 1 := norm_root_eq_one (pow_pos hp.pos _).ne' hw.pow_eq_one
  rw [norm_l, inv_mul_le_iff₀ hl0, ← hp2, aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro j _
  rw [norm_smul, norm_pow, hw1, one_pow, mul_one, ← inv_mul_le_iff₀ hl0]
  exact hb j
