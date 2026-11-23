import Mathlib
import GroundTheory.PAdicHodge.CyclotomicTower
import GroundTheory.PAdicHodge.TiltValuation
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open IntermediateField Polynomial

section Ultra

variable {R : Type*} [NormedField R] [IsUltrametricDist R]

theorem norm_le_norm_sum_of_norm_ne {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → ‖f i‖ = ‖f j‖ → i = j) :
    ∀ i ∈ s, ‖f i‖ ≤ ‖∑ j ∈ s, f j‖ := by
  classical
  intro i hi
  obtain ⟨m, hm, hmax⟩ := s.exists_max_image (fun j => ‖f j‖) ⟨i, hi⟩
  refine (hmax i hi).trans ?_
  rcases eq_or_ne (f m) 0 with h0 | h0
  · rw [h0, norm_zero]; exact norm_nonneg _
  rw [← Finset.add_sum_erase s f hm]
  have hlt : ‖∑ j ∈ s.erase m, f j‖ < ‖f m‖ := by
    rcases (s.erase m).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact norm_pos_iff.2 h0
    · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
      refine hle.trans_lt (lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj)) fun heq => ?_)
      by_cases hj0 : f j = 0
      · rw [hj0, norm_zero] at heq; exact h0 (norm_eq_zero.1 heq.symm)
      · exact (Finset.ne_of_mem_erase hj) (hf j (Finset.mem_of_mem_erase hj) m hm hj0 heq)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne']
  exact le_max_left _ _

end Ultra

variable {p : ℕ} [Fact p.Prime]

theorem exists_eq_sum_sub_one_pow {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {x : PadicAlgCl p} (hx : x ∈ cycl p n) :
    ∃ a : ℕ → ℚ_[p], x = ∑ i ∈ Finset.range (Nat.totient (p ^ n)),
      algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ i := by
  have hint : IsIntegral ℚ_[p] (ζ - 1) := Algebra.IsIntegral.isIntegral _
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = Nat.totient (p ^ n) := by
    rw [IntermediateField.adjoin.powerBasis_dim, ← IntermediateField.adjoin.finrank hint,
      adjoin_sub_one_eq_cycl hζ, finrank_cycl]
  have hx' : x ∈ ℚ_[p]⟮ζ - 1⟯ := by rw [adjoin_sub_one_eq_cycl hζ]; exact hx
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨x, hx'⟩
  refine ⟨fun i => f.coeff i, ?_⟩
  have h1 : x = aeval (ζ - 1) f := by
    have := congrArg (algebraMap (ℚ_[p]⟮ζ - 1⟯) (PadicAlgCl p)) hf
    rw [IntermediateField.adjoin.powerBasis_gen, ← aeval_algebraMap_apply] at this
    exact this
  rw [h1, aeval_eq_sum_range' (hfdeg.trans_eq hdim)]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]

section Ortho

variable {k : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
include hζ

theorem norm_zpow_mul_pow_sub_one_pow (z : ℤ) (m : ℕ) :
    ((p : ℝ) ^ z * ‖ζ - 1‖ ^ m) ^ Nat.totient (p ^ (k + 1)) =
      (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1)) - m) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrd := norm_sub_one_pow_totient hζ
  rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, hrd, inv_pow, ← zpow_natCast ((p : ℝ) ^ z),
    ← zpow_mul, ← zpow_natCast (p : ℝ) m, ← zpow_neg, ← zpow_add₀ hp0]
  ring_nf

theorem norm_coeff_mul_le_norm_sum (a : ℕ → ℚ_[p]) :
    ∀ i ∈ Finset.range (Nat.totient (p ^ (k + 1))),
      ‖a i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ j ∈ Finset.range (Nat.totient (p ^ (k + 1))),
        algebraMap ℚ_[p] (PadicAlgCl p) (a j) * (ζ - 1) ^ j‖ := by
  set d := Nat.totient (p ^ (k + 1))
  have hterm : ∀ i, ‖algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ i‖ = ‖a i‖ * ‖ζ - 1‖ ^ i :=
    fun i => by rw [norm_mul, norm_pow, norm_algebraMap']
  intro i hi
  rw [← hterm]
  refine norm_le_norm_sum_of_norm_ne (R := PadicAlgCl p) (Finset.range d)
    (fun j => algebraMap ℚ_[p] (PadicAlgCl p) (a j) * (ζ - 1) ^ j) (fun i hi j hj hne heq => ?_) i hi
  rw [hterm, hterm] at heq
  have hai : a i ≠ 0 := fun h => hne (by rw [h, map_zero, zero_mul])
  have hr0 : 0 < ‖ζ - 1‖ := by
    have hrd := norm_sub_one_pow_totient hζ
    by_contra h
    have h0 : ‖ζ - 1‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    have hd : d ≠ 0 := (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
    rw [h0, zero_pow hd] at hrd
    exact (inv_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero : (p : ℝ) ≠ 0)) hrd.symm
  have haj : a j ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at heq
    exact (mul_pos (norm_pos_iff.2 hai) (pow_pos hr0 i)).ne' heq
  obtain ⟨zi, hzi⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) hai
  obtain ⟨zj, hzj⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) haj
  rw [hzi, hzj] at heq
  have h2 := congrArg (· ^ d) heq
  rw [norm_zpow_mul_pow_sub_one_pow hζ, norm_zpow_mul_pow_sub_one_pow hζ] at h2
  have h3 := zpow_p_injective (p := p) h2
  have hdvd : (d : ℤ) ∣ ((i : ℤ) - j) := ⟨zi - zj, by linarith⟩
  have hi' := Finset.mem_range.1 hi
  have hj' := Finset.mem_range.1 hj
  have habs : |(i : ℤ) - j| < d := by rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

theorem norm_coeff_le_one {c : ℚ_[p]} {i : ℕ} (hi : i < Nat.totient (p ^ (k + 1)))
    (h : ‖c‖ * ‖ζ - 1‖ ^ i ≤ 1) : ‖c‖ ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero (p := p) hc
  rw [hz] at h ⊢
  have h1 : ((p : ℝ) ^ z * ‖ζ - 1‖ ^ i) ^ Nat.totient (p ^ (k + 1)) ≤ 1 :=
    pow_le_one₀ (mul_nonneg (zpow_nonneg (by positivity) _) (pow_nonneg (norm_nonneg _) _)) h
  rw [norm_zpow_mul_pow_sub_one_pow hζ] at h1
  have h2 := (zpow_le_one_iff_right₀ one_lt_p_real).1 h1
  have hz0 : z ≤ 0 := by
    by_contra hz0
    have hz1 : 1 ≤ z := by omega
    have : (Nat.totient (p ^ (k + 1)) : ℤ) ≤ z * Nat.totient (p ^ (k + 1)) := by
      nlinarith
    omega
  exact zpow_le_one_of_nonpos₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le) hz0

end Ortho

theorem norm_pow_sub_self_le {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) : ‖c ^ p - c‖ ≤ (p : ℝ)⁻¹ := by
  set b : ℤ_[p] := ⟨c, hc⟩
  have h1 : PadicInt.toZMod (b ^ p - b) = 0 := by rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  have h2 : b ^ p - b ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]; exact h1
  have h3 : ‖b ^ p - b‖ < 1 := PadicInt.mem_nonunits.1 h2
  obtain ⟨e, he⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h3
  have h4 : ‖c ^ p - c‖ = ‖b ^ p - b‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [h4, he, norm_mul, PadicInt.norm_p]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one e)

theorem not_isUnit_natCast_normInteger : ¬IsUnit (p : normInteger (PadicAlgCl p)) := by
  rintro ⟨u, hu⟩
  have h1 : ‖((u : normInteger (PadicAlgCl p)) : PadicAlgCl p)‖ *
      ‖((u⁻¹ : (normInteger (PadicAlgCl p))ˣ) : PadicAlgCl p)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, norm_one]
  have hu1 := mem_normInteger.1 (u : normInteger (PadicAlgCl p)).2
  have hv1 := mem_normInteger.1 ((u⁻¹ : (normInteger (PadicAlgCl p))ˣ) : normInteger (PadicAlgCl p)).2
  have hu2 : ‖((u : normInteger (PadicAlgCl p)) : PadicAlgCl p)‖ = 1 := by
    nlinarith [norm_nonneg ((u : normInteger (PadicAlgCl p)) : PadicAlgCl p),
      norm_nonneg (((u⁻¹ : (normInteger (PadicAlgCl p))ˣ) : normInteger (PadicAlgCl p)) : PadicAlgCl p)]
  rw [hu] at hu2
  have : ‖(p : PadicAlgCl p)‖ = 1 := by simpa using hu2
  rw [norm_natCast_prime] at this
  have hp1 : (1 : ℝ) < p := one_lt_p_real
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  linarith

theorem exists_pow_approx_cycl {n : ℕ} {x : PadicAlgCl p} (hx : x ∈ cycl p n) (hx1 : ‖x‖ ≤ 1) :
    ∃ y ∈ cycl p (n + 2), ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : PadicAlgCl p)‖ := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hx' : x ∈ cycl p (n + 1) := cycl_mono (Nat.le_succ n) hx
  obtain ⟨η, hη⟩ := exists_isPrimitiveRoot (p := p) (n + 2)
  have hζ : IsPrimitiveRoot (η ^ p) (p ^ (n + 1)) :=
    hη.pow (pow_pos hp0 _) (by ring)
  set ζ := η ^ p
  set d := Nat.totient (p ^ (n + 1))
  obtain ⟨a, ha⟩ := exists_eq_sum_sub_one_pow hζ hx'
  set b : ℕ → ℚ_[p] := fun i => if i < d then a i else 0
  have hsum : ∀ u : PadicAlgCl p, ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (a i) * u ^ i =
      ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (b i) * u ^ i := fun u =>
    Finset.sum_congr rfl fun i hi => by simp only [b, if_pos (Finset.mem_range.1 hi)]
  have hb1 : ∀ i, ‖b i‖ ≤ 1 := by
    intro i
    by_cases hi : i < d
    · simp only [b, if_pos hi]
      refine norm_coeff_le_one hζ hi ?_
      exact (norm_coeff_mul_le_norm_sum hζ a i (Finset.mem_range.2 hi)).trans (ha ▸ hx1)
    · simp [b, if_neg hi]
  rw [hsum] at ha
  have hηn : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp0.ne') hη.pow_eq_one
  have hη1 : ‖η - 1‖ ≤ 1 := norm_sub_one_le_one (pow_ne_zero _ hp0.ne') hη.pow_eq_one
  have hζn : ‖ζ‖ ≤ 1 := by rw [norm_pow, hηn, one_pow]
  set y := ∑ i ∈ Finset.range d, algebraMap ℚ_[p] (PadicAlgCl p) (b i) * (η - 1) ^ i
  have hy1 : ‖y‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul, norm_pow, norm_algebraMap']
    exact mul_le_one₀ (hb1 i) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hη1)
  have hymem : y ∈ cycl p (n + 2) := by
    refine sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem (sub_mem ?_ (one_mem _)) _)
    exact pow_eq_one_mem_cycl hη.pow_eq_one
  refine ⟨y, hymem, hy1, ?_⟩

  set O := normInteger (PadicAlgCl p)
  have : Fact (¬IsUnit (p : O)) := ⟨not_isUnit_natCast_normInteger⟩
  set A : ℕ → O := fun i => ⟨algebraMap ℚ_[p] (PadicAlgCl p) (b i),
    mem_normInteger.2 (by rw [norm_algebraMap']; exact hb1 i)⟩
  set H : O := ⟨η, mem_normInteger.2 hηn.le⟩
  set Z : O := ⟨ζ, mem_normInteger.2 hζn⟩
  set X : O := ∑ i ∈ Finset.range d, A i * (Z - 1) ^ i
  set Y : O := ∑ i ∈ Finset.range d, A i * (H - 1) ^ i
  have hX : (X : PadicAlgCl p) = x := by
    rw [ha]; simp [X, A, Z, ζ]
  have hY : (Y : PadicAlgCl p) = y := by simp [Y, y, A, H]
  set mk := Ideal.Quotient.mk (Ideal.span {(p : O)})
  have hA : ∀ i, mk (A i) ^ p = mk (A i) := by
    intro i
    rw [← map_pow]
    refine (mk_eq_mk_iff_norm_sub_le (K := PadicAlgCl p)).2 ?_
    have : ((A i ^ p : O) : PadicAlgCl p) - (A i : PadicAlgCl p) =
        algebraMap ℚ_[p] (PadicAlgCl p) (b i ^ p - b i) := by simp [A]
    rw [this, norm_algebraMap', norm_natCast_prime]
    exact norm_pow_sub_self_le (hb1 i)
  have hH : (mk H - 1) ^ p = mk Z - 1 := by
    rw [sub_pow_char, one_pow, ← map_pow]
    congr 2
  have hmk : mk (Y ^ p) = mk X := by
    simp only [Y, X, map_pow, map_sum, map_mul, map_sub, map_one]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, hA, ← pow_mul, mul_comm i p, pow_mul, hH]
  have := (mk_eq_mk_iff_norm_sub_le (K := PadicAlgCl p)).1 hmk.symm
  rw [hX, Subring.coe_pow, hY] at this
  simpa using this

theorem exists_mem_cycl_norm_mem_Ioo {r : ℝ} (hr : r < 1) :
    ∃ n, ∃ x ∈ cycl p n, r < ‖x‖ ∧ ‖x‖ < 1 := by
  have hp1 : (1 : ℝ) < p := one_lt_p_real
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by linarith)
  have hpinv1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1

  obtain ⟨N, hN⟩ : ∃ N : ℕ, max r 0 ^ N < (p : ℝ)⁻¹ := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (le_max_right r 0) (max_lt hr one_pos)
    obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hpinv)).exists_forall_of_atTop
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (N + 1)
  set d := Nat.totient (p ^ (N + 1))
  have hrd := norm_sub_one_pow_totient hζ
  have hd : N ≤ d := by
    have h1 : d = p ^ N * (p - 1) := Nat.totient_prime_pow_succ (Fact.out : p.Prime) N
    have h2 : N < p ^ N := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    have h3 : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
    rw [h1]; nlinarith
  refine ⟨N + 1, ζ - 1, sub_mem (pow_eq_one_mem_cycl hζ.pow_eq_one) (one_mem _), ?_, ?_⟩
  · have h1 : max r 0 ^ d < ‖ζ - 1‖ ^ d := by
      rw [hrd]
      exact lt_of_le_of_lt (pow_le_pow_of_le_one (le_max_right _ _) (max_lt hr one_pos).le hd) hN
    have hd0 : d ≠ 0 := (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
    exact lt_of_le_of_lt (le_max_left r 0)
      ((pow_lt_pow_iff_left₀ (le_max_right _ _) (norm_nonneg _) hd0).1 h1)
  · by_contra h
    have h1 : 1 ≤ ‖ζ - 1‖ ^ d := one_le_pow₀ (not_lt.1 h)
    rw [hrd] at h1
    linarith

end GroundTheory.PAdicHodge
