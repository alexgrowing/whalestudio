import Mathlib
import GroundTheory.PAdicHodge.NormalizedTrace
import GroundTheory.PAdicHodge.CyclotomicField
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormNatCastPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Polynomial Module

noncomputable section

variable {p : ℕ} [Fact p.Prime]

theorem norm_natCast_prime : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ :=
  _root_.UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime

theorem norm_eq_one_of_pow_eq_one {x : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hx : x ^ N = 1) :
    ‖x‖ = 1 := by
  have h : ‖x‖ ^ N = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN).1 h

theorem norm_pow_sub_one_le {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) (j : ℕ) :
    ‖ζ ^ j - 1‖ ≤ ‖ζ - 1‖ := by
  have h1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hN hζ
  rw [← geom_sum_mul, norm_mul]
  have : ‖∑ i ∈ Finset.range j, ζ ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_pow, h1, one_pow]
  calc _ ≤ 1 * ‖ζ - 1‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := one_mul _

theorem norm_sub_one_eq_of_isPrimitiveRoot {ζ η : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0)
    (hζ : IsPrimitiveRoot ζ N) (hη : IsPrimitiveRoot η N) : ‖η - 1‖ = ‖ζ - 1‖ := by
  have : NeZero N := ⟨hN⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη.pow_eq_one
  obtain ⟨j, -, hj⟩ := hη.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine le_antisymm (norm_pow_sub_one_le hN hζ.pow_eq_one i) ?_
  conv_lhs => rw [← hj]
  exact norm_pow_sub_one_le hN hη.pow_eq_one j

theorem norm_sub_one_pow_totient {ζ : PadicAlgCl p} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    ‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1)) = (p : ℝ)⁻¹ := by
  have hpos : 0 < p ^ (k + 1) := pow_pos (Fact.out : p.Prime).pos _
  have h1 := congrArg (eval 1) (cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
  rw [eval_one_cyclotomic_prime_pow, eval_prod] at h1
  simp only [eval_sub, eval_X, eval_C] at h1
  rw [← norm_natCast_prime]
  calc ‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1))
      = ∏ _μ ∈ primitiveRoots (p ^ (k + 1)) (PadicAlgCl p), ‖ζ - 1‖ := by
        rw [Finset.prod_const, hζ.card_primitiveRoots]
    _ = ∏ μ ∈ primitiveRoots (p ^ (k + 1)) (PadicAlgCl p), ‖1 - μ‖ :=
        Finset.prod_congr rfl fun μ hμ => by
          rw [norm_sub_rev 1 μ]
          exact (norm_sub_one_eq_of_isPrimitiveRoot hpos.ne' hζ
            ((mem_primitiveRoots hpos).1 hμ)).symm
    _ = _ := by rw [h1, norm_prod]

theorem norm_sub_one_le_one {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (hζ : ζ ^ N = 1) :
    ‖ζ - 1‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max ζ (-1)
  rw [← sub_eq_add_neg, norm_neg, norm_one, norm_eq_one_of_pow_eq_one hN hζ, max_self] at this
  exact this

theorem norm_pow_natDegree_minpoly (y : PadicAlgCl p) :
    ‖y‖ ^ (minpoly ℚ_[p] y).natDegree = ‖(minpoly ℚ_[p] y).coeff 0‖ := by
  have hd : (minpoly ℚ_[p] y).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)).ne'
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
    Real.rpow_inv_natCast_pow (norm_nonneg _) hd]

theorem exists_norm_eq_zpow_of_ne_zero {c : ℚ_[p]} (hc : c ≠ 0) : ∃ z : ℤ, ‖c‖ = (p : ℝ) ^ z :=
  ⟨-c.valuation, Padic.norm_eq_zpow_neg_valuation hc⟩

theorem one_lt_p_real : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

theorem zpow_p_injective : Function.Injective fun z : ℤ => (p : ℝ) ^ z :=
  zpow_right_injective₀ (by linarith [one_lt_p_real (p := p)]) (one_lt_p_real (p := p)).ne'

theorem minpoly_eq_cyclotomic_of_isPrimitiveRoot {ζ : PadicAlgCl p} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    minpoly ℚ_[p] ζ = cyclotomic (p ^ (k + 1)) ℚ_[p] := by
  have hpos : 0 < p ^ (k + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hint : IsIntegral ℚ_[p] ζ := Algebra.IsIntegral.isIntegral ζ
  have hdvd : minpoly ℚ_[p] ζ ∣ cyclotomic (p ^ (k + 1)) ℚ_[p] := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hpos
  set d := (minpoly ℚ_[p] ζ).natDegree with hd
  have hφ : 0 < Nat.totient (p ^ (k + 1)) := Nat.totient_pos.2 hpos
  have hd0 : 0 < d := minpoly.natDegree_pos hint

  have hπdeg : (minpoly ℚ_[p] (ζ - 1)).natDegree = d := by
    have : ζ - 1 = ζ - algebraMap ℚ_[p] (PadicAlgCl p) 1 := by rw [map_one]
    rw [this, minpoly.sub_algebraMap, natDegree_comp, natDegree_X_add_C, mul_one]
  have hπ0 : ζ - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have := hζ.pow_ne_one_of_pos_of_lt one_ne_zero (Nat.one_lt_pow (Nat.succ_ne_zero k)
      (Fact.out : p.Prime).one_lt)
    exact this (by rw [pow_one, h])
  have hc0 : (minpoly ℚ_[p] (ζ - 1)).coeff 0 ≠ 0 :=
    minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral _) hπ0
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero hc0
  have e1 := norm_pow_natDegree_minpoly (ζ - 1)
  rw [hπdeg, hz] at e1
  have e2 := norm_sub_one_pow_totient hζ

  have key : (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1))) = (p : ℝ) ^ (-(d : ℤ)) := by
    calc (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1)))
        = ((p : ℝ) ^ z) ^ Nat.totient (p ^ (k + 1)) := by rw [zpow_mul, zpow_natCast]
      _ = (‖ζ - 1‖ ^ d) ^ Nat.totient (p ^ (k + 1)) := by rw [e1]
      _ = (‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1))) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((p : ℝ)⁻¹) ^ d := by rw [e2]
      _ = (p : ℝ) ^ (-(d : ℤ)) := by rw [zpow_neg, zpow_natCast, inv_pow]
  have key' := zpow_p_injective (p := p) key
  have hdvdφ : Nat.totient (p ^ (k + 1)) ∣ d := by
    have : ((Nat.totient (p ^ (k + 1)) : ℕ) : ℤ) ∣ (d : ℤ) :=
      ⟨-z, by linear_combination key'⟩
    exact Int.natCast_dvd_natCast.1 this
  have hle1 : Nat.totient (p ^ (k + 1)) ≤ d := Nat.le_of_dvd hd0 hdvdφ
  have hle2 : d ≤ Nat.totient (p ^ (k + 1)) := by
    rw [← natDegree_cyclotomic (p ^ (k + 1)) ℚ_[p]]
    exact natDegree_le_of_dvd hdvd (cyclotomic_ne_zero _ _)
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _) hdvd
    (by rw [natDegree_cyclotomic]; omega)).symm

theorem irreducible_cyclotomic_prime_pow (n : ℕ) : Irreducible (cyclotomic (p ^ n) ℚ_[p]) := by
  cases n with
  | zero => simpa using irreducible_X_sub_C (1 : ℚ_[p])
  | succ k =>
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
    rw [← minpoly_eq_cyclotomic_of_isPrimitiveRoot hζ]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral ζ)

theorem finrank_cycl (n : ℕ) : finrank ℚ_[p] (cycl p n) = Nat.totient (p ^ n) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) n
  rw [cycl_eq_adjoin hζ, IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)]
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hζ
    subst hζ
    rw [minpoly.one]
    simpa using natDegree_X_sub_C (1 : ℚ_[p])
  | succ k => rw [minpoly_eq_cyclotomic_of_isPrimitiveRoot hζ, natDegree_cyclotomic]

theorem totient_prime_pow_succ {k : ℕ} (hk : 1 ≤ k) :
    Nat.totient (p ^ (k + 1)) = p * Nat.totient (p ^ k) := by
  rw [pow_succ', Nat.totient_mul_of_prime_of_dvd (Fact.out : p.Prime)
    (dvd_pow_self p (by omega))]

theorem natDegree_minpoly_cycl_of_adjoin_eq {k : ℕ} (hk : 1 ≤ k) {y : PadicAlgCl p}
    (hy : ℚ_[p]⟮y⟯ = cycl p (k + 1)) : (minpoly (cycl p k) y).natDegree = p := by
  have hint : IsIntegral (cycl p k) y :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  have e := finrank_sup_adjoin_simple (cycl p k) hint
  rw [hy, sup_eq_right.2 (cycl_mono (Nat.le_succ k)), finrank_cycl, finrank_cycl,
    totient_prime_pow_succ hk] at e
  have hφ : 0 < Nat.totient (p ^ k) := Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)
  rw [mul_comm p] at e
  exact (Nat.eq_of_mul_eq_mul_left hφ e).symm

theorem normTrace_cycl_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) : normTrace (cycl p k) η = 0 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hint : IsIntegral (cycl p k) η :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) η).tower_top
  have hdeg := natDegree_minpoly_cycl_of_adjoin_eq hk (cycl_eq_adjoin hη).symm
  have hc : η ^ p ∈ cycl p k := pow_eq_one_mem_cycl (by rw [← pow_mul, ← pow_succ']; exact hη.pow_eq_one)
  set f : (cycl p k)[X] := X ^ p - C ⟨η ^ p, hc⟩ with hf
  have hfm : f.Monic := monic_X_pow_sub_C _ (by omega)
  have hfdeg : f.natDegree = p := natDegree_X_pow_sub_C
  have hroot : aeval η f = 0 := by simp [hf]
  have hdvd : minpoly (cycl p k) η ∣ f := minpoly.dvd _ _ hroot
  have heq : f = minpoly (cycl p k) η :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hfm hdvd (by rw [hfdeg, hdeg])
  have hnext : f.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hfdeg, hf, coeff_sub, coeff_X_pow, coeff_C]
    simp only [if_neg (show p - 1 ≠ p by omega), if_neg (show p - 1 ≠ 0 by omega), sub_zero]
  rw [normTrace, normTraceF, ← heq, hnext]
  simp

theorem exists_norm_pow_totient_eq_zpow {n : ℕ} {y : PadicAlgCl p} (hy : y ∈ cycl p n)
    (hy0 : y ≠ 0) : ∃ z : ℤ, ‖y‖ ^ Nat.totient (p ^ n) = (p : ℝ) ^ z := by
  have hint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  have hle : ℚ_[p]⟮y⟯ ≤ cycl p n := by rw [adjoin_simple_le_iff]; exact hy
  have hdvd : (minpoly ℚ_[p] y).natDegree ∣ Nat.totient (p ^ n) := by
    rw [← finrank_cycl, finrank_eq_mul_finrank_extendScalars hle,
      IntermediateField.adjoin.finrank hint]
    exact Dvd.intro _ rfl
  obtain ⟨m, hm⟩ := hdvd
  have hc0 : (minpoly ℚ_[p] y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy0
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero hc0
  refine ⟨z * m, ?_⟩
  rw [hm, pow_mul, norm_pow_natDegree_minpoly, hz, zpow_mul, zpow_natCast]

variable (p) in

def cyclRadius (j : ℕ) : ℝ := ‖(exists_isPrimitiveRoot (p := p) j).choose - 1‖

theorem norm_sub_one_eq_cyclRadius {η : PadicAlgCl p} {j : ℕ} (hη : IsPrimitiveRoot η (p ^ j)) :
    ‖η - 1‖ = cyclRadius p j :=
  norm_sub_one_eq_of_isPrimitiveRoot (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    (exists_isPrimitiveRoot (p := p) j).choose_spec hη

theorem cyclRadius_nonneg (j : ℕ) : 0 ≤ cyclRadius p j := norm_nonneg _

theorem cyclRadius_pow_totient (k : ℕ) :
    cyclRadius p (k + 1) ^ Nat.totient (p ^ (k + 1)) = (p : ℝ)⁻¹ := by
  rw [← norm_sub_one_eq_cyclRadius (exists_isPrimitiveRoot (p := p) (k + 1)).choose_spec]
  exact norm_sub_one_pow_totient (exists_isPrimitiveRoot (p := p) (k + 1)).choose_spec

theorem cyclRadius_le_one (j : ℕ) : cyclRadius p j ≤ 1 :=
  norm_sub_one_le_one (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    (exists_isPrimitiveRoot (p := p) j).choose_spec.pow_eq_one

theorem inv_p_le_cyclRadius (k : ℕ) : (p : ℝ)⁻¹ ≤ cyclRadius p (k + 1) := by
  rw [← cyclRadius_pow_totient k]
  exact pow_le_of_le_one (norm_nonneg _) (cyclRadius_le_one _)
    (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'

theorem cyclRadius_pos (k : ℕ) : 0 < cyclRadius p (k + 1) :=
  lt_of_lt_of_le (inv_pos.2 (by exact_mod_cast (Fact.out : p.Prime).pos)) (inv_p_le_cyclRadius k)

theorem cyclRadius_succ_pow {k : ℕ} (hk : 1 ≤ k) : cyclRadius p (k + 1) ^ p = cyclRadius p k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hφ : Nat.totient (p ^ (j + 1)) ≠ 0 :=
    (Nat.totient_pos.2 (pow_pos (Fact.out : p.Prime).pos _)).ne'
  refine (pow_left_inj₀ (pow_nonneg (cyclRadius_nonneg (p := p) _) _) (cyclRadius_nonneg (p := p) _)
    hφ).1 ?_
  rw [← pow_mul, ← totient_prime_pow_succ (p := p) (k := j + 1) (by omega),
    cyclRadius_pow_totient (p := p) (j + 1), cyclRadius_pow_totient (p := p) j]

theorem cyclRadius_succ_pow_pred {k : ℕ} (hk : 1 ≤ k) :
    cyclRadius p (k + 1) ^ (p - 1) = cyclRadius p k / cyclRadius p (k + 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h : cyclRadius p (k + 1) ^ (p - 1) * cyclRadius p (k + 1) = cyclRadius p k := by
    rw [← pow_succ, Nat.sub_add_cancel hp, cyclRadius_succ_pow (p := p) hk]
  rw [eq_div_iff (cyclRadius_pos (p := p) k).ne', h]

theorem adjoin_sub_one_eq_cycl {ζ : PadicAlgCl p} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    ℚ_[p]⟮ζ - 1⟯ = cycl p n := by
  rw [cycl_eq_adjoin hζ]
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact sub_mem (mem_adjoin_simple_self ℚ_[p] ζ) (one_mem _)
  · rw [adjoin_simple_le_iff]
    have h := add_mem (mem_adjoin_simple_self ℚ_[p] (ζ - 1)) (one_mem ℚ_[p]⟮ζ - 1⟯)
    rwa [sub_add_cancel] at h

theorem exists_eq_sum_pow_of_adjoin_eq {k : ℕ} (hk : 1 ≤ k) {y : PadicAlgCl p}
    (hy : ℚ_[p]⟮y⟯ = cycl p (k + 1)) {x : PadicAlgCl p} (hx : x ∈ cycl p (k + 1)) :
    ∃ b : ℕ → PadicAlgCl p, (∀ i, b i ∈ cycl p k) ∧ x = ∑ i ∈ Finset.range p, b i * y ^ i := by
  have hint : IsIntegral (cycl p k) y :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = p := by
    rw [IntermediateField.adjoin.powerBasis_dim, natDegree_minpoly_cycl_of_adjoin_eq hk hy]
  have hx' : x ∈ (cycl p k)⟮y⟯ := by
    have : cycl p (k + 1) ≤ ((cycl p k)⟮y⟯).restrictScalars ℚ_[p] := by
      rw [← hy, adjoin_simple_le_iff, mem_restrictScalars]
      exact mem_adjoin_simple_self _ y
    exact this hx
  obtain ⟨f, hfdeg, hf⟩ := pb.exists_eq_aeval ⟨x, hx'⟩
  refine ⟨fun i => algebraMap (cycl p k) (PadicAlgCl p) (f.coeff i), fun i => (f.coeff i).2, ?_⟩
  have h1 : x = aeval y f := by
    have := congrArg (algebraMap ((cycl p k)⟮y⟯) (PadicAlgCl p)) hf
    rw [IntermediateField.adjoin.powerBasis_gen, ← aeval_algebraMap_apply] at this
    exact this
  rw [h1, aeval_eq_sum_range' (hfdeg.trans_eq hdim)]
  exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def]

theorem norm_mul_pow_le_norm_sum {k : ℕ} (hk : 1 ≤ k) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {b : ℕ → PadicAlgCl p} (hb : ∀ i, b i ∈ cycl p k) :
    ∀ i ∈ Finset.range p, ‖b i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ i ∈ Finset.range p, b i * (ζ - 1) ^ i‖ := by
  set π := ζ - 1
  set x := ∑ i ∈ Finset.range p, b i * π ^ i
  set φ := Nat.totient (p ^ k)
  have hπpow : ‖π‖ ^ (p * φ) = (p : ℝ)⁻¹ := by
    rw [← totient_prime_pow_succ hk]; exact norm_sub_one_pow_totient hζ

  have hterm : ∀ i, b i ≠ 0 → ∃ z : ℤ, (‖b i‖ * ‖π‖ ^ i) ^ (p * φ) = (p : ℝ) ^ ((p : ℤ) * z - i) := by
    intro i hi
    obtain ⟨z, hz⟩ := exists_norm_pow_totient_eq_zpow (hb i) hi
    refine ⟨z, ?_⟩
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    calc (‖b i‖ * ‖π‖ ^ i) ^ (p * φ) = (‖b i‖ ^ φ) ^ p * (‖π‖ ^ (p * φ)) ^ i := by ring
      _ = ((p : ℝ) ^ z) ^ p * ((p : ℝ)⁻¹) ^ i := by rw [hz, hπpow]
      _ = (p : ℝ) ^ ((p : ℤ) * z - i) := by
        rw [← zpow_natCast ((p : ℝ) ^ z) p, ← zpow_mul, inv_pow, ← zpow_natCast (p : ℝ) i,
          ← zpow_neg, ← zpow_add₀ hp0]
        congr 1; ring
  have hdistinct : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range p, i ≠ j → b i ≠ 0 → b j ≠ 0 →
      ‖b i‖ * ‖π‖ ^ i ≠ ‖b j‖ * ‖π‖ ^ j := by
    intro i hi j hj hij hbi hbj h
    obtain ⟨zi, hzi⟩ := hterm i hbi
    obtain ⟨zj, hzj⟩ := hterm j hbj
    have := zpow_p_injective (p := p) (hzi.symm.trans ((congrArg (· ^ (p * φ)) h).trans hzj))
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have hdvd : (p : ℤ) ∣ ((i : ℤ) - j) := ⟨zi - zj, by linear_combination (-1 : ℤ) * this⟩
    have habs : |(i : ℤ) - j| < p := by rw [abs_lt]; constructor <;> omega
    exact hij (by have := Int.eq_zero_of_abs_lt_dvd hdvd habs; omega)
  intro i hi
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (Finset.range p) (fun i => ‖b i‖ * ‖π‖ ^ i)
    ⟨i, hi⟩
  set M := ‖b i0‖ * ‖π‖ ^ i0
  have hxM : ‖x‖ < M := lt_of_lt_of_le hlt (hmax i hi)
  have hM0 : 0 < M := lt_of_le_of_lt (norm_nonneg _) hxM
  have hbi0 : b i0 ≠ 0 := by
    intro h; rw [show M = 0 by simp [M, h]] at hM0; exact lt_irrefl 0 hM0
  have hlt' : ∀ j ∈ (Finset.range p).erase i0, ‖b j * π ^ j‖ < M := by
    intro j hj
    rw [norm_mul, norm_pow]
    rcases eq_or_ne (b j) 0 with h | h
    · rw [h, norm_zero, zero_mul]; exact hM0
    · exact lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj))
        (hdistinct j (Finset.mem_of_mem_erase hj) i0 hi0 (Finset.ne_of_mem_erase hj) h hbi0)
  set rest := ∑ j ∈ (Finset.range p).erase i0, b j * π ^ j
  have hrest : ‖rest‖ < M := by
    rcases ((Finset.range p).erase i0).eq_empty_or_nonempty with h | h
    · rw [show rest = 0 by simp [rest, h], norm_zero]; exact hM0
    · obtain ⟨j, hj, hjle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun j => b j * π ^ j)
      exact lt_of_le_of_lt hjle (hlt' j hj)
  have hx : x = b i0 * π ^ i0 + rest := (Finset.add_sum_erase _ _ hi0).symm
  have : ‖b i0 * π ^ i0‖ ≤ max ‖x‖ ‖rest‖ := by
    have h1 := IsUltrametricDist.norm_add_le_max x (-rest)
    rw [norm_neg] at h1
    calc ‖b i0 * π ^ i0‖ = ‖x + -rest‖ := by rw [hx, add_neg_cancel_right]
      _ ≤ max ‖x‖ ‖rest‖ := h1
  rw [norm_mul, norm_pow] at this
  exact absurd this (not_le.2 (max_lt hxM hrest))

theorem normTrace_cycl_sub_one_pow {k : ℕ} (hk : 1 ≤ k) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {i : ℕ} (hi : i < p) :
    normTrace (cycl p k) ((ζ - 1) ^ i) = (-1) ^ i := by
  have hpr := (Fact.out : p.Prime)
  rw [sub_eq_add_neg, add_pow, normTrace_sum]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    exact normTrace_of_mem _ (pow_mem (neg_mem (one_mem _)) _)
  · intro j hj hj0
    have hjp : j < p := lt_of_lt_of_le (Finset.mem_range.1 hj) (by omega)
    have hmem : (-1 : PadicAlgCl p) ^ (i - j) * (i.choose j : PadicAlgCl p) ∈ cycl p k :=
      mul_mem (pow_mem (neg_mem (one_mem _)) _) (IntermediateField.natCast_mem _ _)
    rw [mul_assoc, mul_comm, normTrace_mul_of_mem _ hmem]
    have hcop : j.Coprime (p ^ (k + 1)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpr).2
        fun h => by have := Nat.le_of_dvd (by omega) h; omega))
    rw [normTrace_cycl_isPrimitiveRoot hk (hζ.pow_of_coprime j hcop), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos i)) h

theorem norm_normTrace_cycl_succ_mul_le {k : ℕ} (hk : 1 ≤ k) {x : PadicAlgCl p}
    (hx : x ∈ cycl p (k + 1)) :
    ‖normTrace (cycl p k) x‖ * cyclRadius p (k + 1) ^ (p - 1) ≤ ‖x‖ := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
  obtain ⟨b, hb, rfl⟩ := exists_eq_sum_pow_of_adjoin_eq hk (adjoin_sub_one_eq_cycl hζ) hx
  have horth := norm_mul_pow_le_norm_sum hk hζ hb
  set x := ∑ i ∈ Finset.range p, b i * (ζ - 1) ^ i
  have hr := cyclRadius_pos (p := p) k
  have hrpow : 0 < cyclRadius p (k + 1) ^ (p - 1) := pow_pos hr _
  have hrad : ‖ζ - 1‖ = cyclRadius p (k + 1) := norm_sub_one_eq_cyclRadius hζ
  have htr : normTrace (cycl p k) x = ∑ i ∈ Finset.range p, b i * (-1) ^ i := by
    rw [normTrace_sum]
    exact Finset.sum_congr rfl fun i hi => by
      rw [normTrace_mul_of_mem _ (hb i), normTrace_cycl_sub_one_pow hk hζ (Finset.mem_range.1 hi)]
  rw [htr, ← le_div_iff₀ hrpow]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (div_nonneg (norm_nonneg _) hrpow.le) fun i hi => ?_
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, le_div_iff₀ hrpow]
  calc ‖b i‖ * cyclRadius p (k + 1) ^ (p - 1) ≤ ‖b i‖ * ‖ζ - 1‖ ^ i := by
        rw [hrad]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr.le (cyclRadius_le_one _)
          (by have := Finset.mem_range.1 hi; omega)) (norm_nonneg _)
    _ ≤ ‖x‖ := horth i hi

theorem norm_normTrace_cycl_mul_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {x : PadicAlgCl p}
    (hx : x ∈ cycl p m) :
    ‖normTrace (cycl p n) x‖ * cyclRadius p n ≤ ‖x‖ * cyclRadius p m := by
  induction m, hnm using Nat.le_induction generalizing x with
  | base => rw [normTrace_of_mem _ hx]
  | succ m hnm ih =>
    have hm : 1 ≤ m := le_trans hn hnm
    rw [← normTrace_normTrace_of_le (cycl_mono hnm) x]
    have h1 := ih (normTrace_mem (cycl p m) x)
    have h2 := norm_normTrace_cycl_succ_mul_le hm hx
    rw [cyclRadius_succ_pow_pred hm, mul_div_assoc', div_le_iff₀ (cyclRadius_pos (p := p) m)] at h2
    exact h1.trans h2

theorem norm_normTrace_cycl_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) {x : PadicAlgCl p}
    (hx : x ∈ cycl p m) : ‖normTrace (cycl p n) x‖ ≤ p * ‖x‖ := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have h := norm_normTrace_cycl_mul_le hn hnm hx
  have hr := cyclRadius_pos (p := p) j
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : ‖normTrace (cycl p (j + 1)) x‖ * cyclRadius p (j + 1) ≤ ‖x‖ :=
    h.trans (mul_le_of_le_one_right (norm_nonneg _) (cyclRadius_le_one _))
  have h2 : (p : ℝ)⁻¹ ≤ cyclRadius p (j + 1) := inv_p_le_cyclRadius j
  calc ‖normTrace (cycl p (j + 1)) x‖ = p * (‖normTrace (cycl p (j + 1)) x‖ * (p : ℝ)⁻¹) := by
        field_simp
    _ ≤ p * (‖normTrace (cycl p (j + 1)) x‖ * cyclRadius p (j + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) hp0.le
    _ ≤ p * ‖x‖ := mul_le_mul_of_nonneg_left h1 hp0.le

theorem norm_algEquiv_apply (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    ‖γ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv γ x).symm

theorem norm_pow_apply_sub_le (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : PadicAlgCl p)
    (N : ℕ) : ‖(γ ^ N) y - y‖ ≤ ‖γ y - y‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (γ ^ (N + 1)) y - y = (γ ^ N) (γ y - y) + ((γ ^ N) y - y) := by
      rw [pow_succ, AlgEquiv.mul_apply, map_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    rw [norm_algEquiv_apply]

theorem exists_apply_eq_mul_of_fix {k : ℕ} (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1))) :
    ∃ ε : PadicAlgCl p, ε ^ p = 1 ∧ τ η = ε * η := by
  have hη0 : η ≠ 0 := hη.ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hc : η ^ p ∈ cycl p k :=
    pow_eq_one_mem_cycl (by rw [← pow_mul, ← pow_succ']; exact hη.pow_eq_one)
  refine ⟨τ η * η⁻¹, ?_, by field_simp⟩
  rw [mul_pow, inv_pow, ← map_pow, hτ _ hc, mul_inv_cancel₀ (pow_ne_zero _ hη0)]

theorem mem_cycl_of_pow_prime_eq_one {k : ℕ} (hk : 1 ≤ k) {ε : PadicAlgCl p} (hε : ε ^ p = 1) :
    ε ∈ cycl p k := by
  apply pow_eq_one_mem_cycl
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ', pow_mul, hε, one_pow]

theorem inv_p_le_norm_pow_sub_one {ε : PadicAlgCl p} (hε : ε ^ p = 1) (hε1 : ε ≠ 1) {i : ℕ}
    (hi0 : 1 ≤ i) (hip : i < p) : (p : ℝ)⁻¹ ≤ ‖ε ^ i - 1‖ := by
  have hpr := (Fact.out : p.Prime)
  have hprim : IsPrimitiveRoot ε p := by
    have := IsPrimitiveRoot.orderOf ε
    rwa [orderOf_eq_prime hε hε1] at this
  have hcop : i.Coprime p :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpr).2 fun h => by
      have := Nat.le_of_dvd (by omega) h; omega)
  have hprim' : IsPrimitiveRoot (ε ^ i) (p ^ (0 + 1)) := by
    rw [zero_add, pow_one]; exact hprim.pow_of_coprime i hcop
  have h := norm_sub_one_pow_totient hprim'
  rw [← h]
  exact pow_le_of_le_one (norm_nonneg _)
    (norm_sub_one_le_one (pow_ne_zero _ hpr.ne_zero) hprim'.pow_eq_one)
    (Nat.totient_pos.2 (pow_pos hpr.pos _)).ne'

def cyclCoord (k : ℕ) (η y : PadicAlgCl p) (i : ℕ) : PadicAlgCl p :=
  normTrace (cycl p k) (y * η ^ (p ^ (k + 1) - i))

theorem cyclCoord_mem (k : ℕ) (η y : PadicAlgCl p) (i : ℕ) : cyclCoord k η y i ∈ cycl p k :=
  normTrace_mem _ _

theorem cyclCoord_zero {k : ℕ} {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (y : PadicAlgCl p) : cyclCoord k η y 0 = normTrace (cycl p k) y := by
  rw [cyclCoord, Nat.sub_zero, hη.pow_eq_one, mul_one]

theorem cyclCoord_sub (k : ℕ) (η y y' : PadicAlgCl p) (i : ℕ) :
    cyclCoord k η (y - y') i = cyclCoord k η y i - cyclCoord k η y' i := by
  rw [cyclCoord, cyclCoord, cyclCoord, sub_mul, normTrace_sub]

theorem eq_sum_cyclCoord {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) :
    y = ∑ i ∈ Finset.range p, cyclCoord k η y i * η ^ i := by
  have hpr := (Fact.out : p.Prime)
  obtain ⟨b, hb, hyb⟩ := exists_eq_sum_pow_of_adjoin_eq hk (cycl_eq_adjoin hη).symm hy
  have hcoord : ∀ i ∈ Finset.range p, cyclCoord k η y i = b i := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hle : i ≤ p ^ (k + 1) := le_trans hi'.le (Nat.le_self_pow (by omega) p)
    rw [cyclCoord, hyb, Finset.sum_mul, normTrace_sum, Finset.sum_eq_single i]
    · rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle, hη.pow_eq_one, mul_one,
        normTrace_of_mem _ (hb i)]
    · intro j hj hji
      have hj' := Finset.mem_range.1 hj
      rw [mul_assoc, ← pow_add, normTrace_mul_of_mem _ (hb j)]
      have hcop : (j + (p ^ (k + 1) - i)).Coprime (p ^ (k + 1)) := by
        refine Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpr).2
          fun h => hji ?_))
        have h' : (p : ℤ) ∣ ((j : ℤ) - i) := by
          have e : ((j + (p ^ (k + 1) - i) : ℕ) : ℤ) = (p : ℤ) * (p : ℤ) ^ k + ((j : ℤ) - i) := by
            push_cast [Nat.cast_sub hle]; ring
          have h2 : (p : ℤ) ∣ ((j + (p ^ (k + 1) - i) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h
          rw [e] at h2
          exact (dvd_add_right (dvd_mul_right _ _)).1 h2
        have habs : |(j : ℤ) - i| < p := by rw [abs_lt]; constructor <;> omega
        have := Int.eq_zero_of_abs_lt_dvd h' habs
        omega
      rw [normTrace_cycl_isPrimitiveRoot hk (hη.pow_of_coprime _ hcop), mul_zero]
    · intro h; exact absurd hi h
  calc y = ∑ i ∈ Finset.range p, b i * η ^ i := hyb
    _ = _ := Finset.sum_congr rfl fun i hi => by rw [hcoord i hi]

theorem norm_cyclCoord_le {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) (i : ℕ) :
    ‖cyclCoord k η y i‖ ≤ p * ‖y‖ := by
  have hηmem : η ∈ cycl p (k + 1) := pow_eq_one_mem_cycl hη.pow_eq_one
  have h := norm_normTrace_cycl_le hk (Nat.le_succ k) (mul_mem hy (pow_mem hηmem (p ^ (k + 1) - i)))
  rwa [norm_mul, norm_pow, norm_eq_one_of_pow_eq_one (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    hη.pow_eq_one, one_pow, mul_one] at h

theorem cyclCoord_apply {k : ℕ} (hk : 1 ≤ k) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η ε : PadicAlgCl p} (hεp : ε ^ p = 1) (hτη : τ η = ε * η)
    (y : PadicAlgCl p) {i : ℕ} (hi : i ≤ p ^ (k + 1)) :
    cyclCoord k η (τ y) i = ε ^ i * cyclCoord k η y i := by
  have hεk : ε ∈ cycl p k := mem_cycl_of_pow_prime_eq_one hk hεp
  have hε1 : ε ^ (p ^ (k + 1)) = 1 := by rw [pow_succ', pow_mul, hεp, one_pow]
  have e : τ y * η ^ (p ^ (k + 1) - i) = ε ^ i * τ (y * η ^ (p ^ (k + 1) - i)) := by
    rw [map_mul, map_pow, hτη, mul_pow]
    calc τ y * η ^ (p ^ (k + 1) - i)
        = τ y * (ε ^ (i + (p ^ (k + 1) - i)) * η ^ (p ^ (k + 1) - i)) := by
          rw [Nat.add_sub_cancel' hi, hε1, one_mul]
      _ = _ := by rw [pow_add]; ring
  rw [cyclCoord, e, normTrace_mul_of_mem _ (pow_mem hεk i),
    normTrace_map_of_map_eq (cycl p k) τ (cycl_map τ k), hτ _ (normTrace_mem _ _), cyclCoord]

theorem norm_le_of_normTrace_cycl_succ_eq_zero {k : ℕ} (hk : 1 ≤ k)
    (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hτ : ∀ x ∈ cycl p k, τ x = x)
    {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1))) (hτη : τ η ≠ η)
    {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) (h0 : normTrace (cycl p k) y = 0) :
    ‖y‖ ≤ (p : ℝ) ^ 2 * ‖τ y - y‖ := by
  have hpr := (Fact.out : p.Prime)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
  obtain ⟨ε, hεp, hτη'⟩ := exists_apply_eq_mul_of_fix τ hτ hη
  have hε1 : ε ≠ 1 := by rintro rfl; rw [one_mul] at hτη'; exact hτη hτη'
  have hτy : τ y ∈ cycl p (k + 1) := map_mem_cycl τ hy
  have hw : τ y - y ∈ cycl p (k + 1) := sub_mem hτy hy
  have hcoord : ∀ i ∈ Finset.range p, ‖cyclCoord k η y i‖ ≤ (p : ℝ) ^ 2 * ‖τ y - y‖ := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [cyclCoord_zero hη, h0, norm_zero]; positivity
    have hle : i ≤ p ^ (k + 1) := le_trans hi'.le (Nat.le_self_pow (by omega) p)
    have e : cyclCoord k η (τ y - y) i = (ε ^ i - 1) * cyclCoord k η y i := by
      rw [cyclCoord_sub, cyclCoord_apply hk τ hτ hεp hτη' y hle]; ring
    have h1 := norm_cyclCoord_le hk hη hw i
    rw [e, norm_mul] at h1
    have h2 := inv_p_le_norm_pow_sub_one hεp hε1 hipos hi'
    have h3 : (p : ℝ)⁻¹ * ‖cyclCoord k η y i‖ ≤ p * ‖τ y - y‖ :=
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1
    calc ‖cyclCoord k η y i‖ = p * ((p : ℝ)⁻¹ * ‖cyclCoord k η y i‖) := by field_simp
      _ ≤ p * (p * ‖τ y - y‖) := mul_le_mul_of_nonneg_left h3 hp0.le
      _ = _ := by ring
  conv_lhs => rw [eq_sum_cyclCoord hk hη hy]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
  rw [norm_mul, norm_pow, norm_eq_one_of_pow_eq_one (pow_ne_zero _ hpr.ne_zero) hη.pow_eq_one,
    one_pow, mul_one]
  exact hcoord i hi

theorem apply_ne_of_isPrimitiveRoot {k : ℕ} (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (hτη : τ η ≠ η) {η' : PadicAlgCl p} (hη' : IsPrimitiveRoot η' (p ^ (k + 1))) : τ η' ≠ η' := by
  have hpr := (Fact.out : p.Prime)
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hpr.ne_zero⟩
  obtain ⟨ε, hεp, hτη'⟩ := exists_apply_eq_mul_of_fix τ hτ hη
  have hε1 : ε ≠ 1 := by rintro rfl; rw [one_mul] at hτη'; exact hτη hτη'
  have hprim : IsPrimitiveRoot ε p := by
    have := IsPrimitiveRoot.orderOf ε
    rwa [orderOf_eq_prime hεp hε1] at this
  obtain ⟨j, -, rfl⟩ := hη.eq_pow_of_pow_eq_one hη'.pow_eq_one
  have hj : ¬ p ∣ j := by
    intro h
    obtain ⟨c, rfl⟩ := h
    have := hη'.pow_eq_one_iff_dvd (p ^ k)
    have h2 : (η ^ (p * c)) ^ (p ^ k) = 1 := by
      rw [← pow_mul, show p * c * p ^ k = p ^ (k + 1) * c by ring, pow_mul, hη.pow_eq_one, one_pow]
    have h3 := this.1 h2
    have h4 := Nat.le_of_dvd (pow_pos hpr.pos _) h3
    have h5 : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hpr.one_lt (by omega)
    omega
  rw [map_pow, hτη', mul_pow]
  intro h
  have hη0 : η ^ j ≠ 0 := pow_ne_zero _ (hη.ne_zero (pow_ne_zero _ hpr.ne_zero))
  have : ε ^ j = 1 := by
    have := congrArg (· * (η ^ j)⁻¹) h
    simpa [mul_assoc, mul_inv_cancel₀ hη0] using this
  exact hj ((hprim.pow_eq_one_iff_dvd j).1 this)

theorem pow_prime_fix_cycl_succ {k : ℕ} (hk : 1 ≤ k) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) : ∀ x ∈ cycl p (k + 1), (τ ^ p) x = x := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
  obtain ⟨ε, hεp, hτζ⟩ := exists_apply_eq_mul_of_fix τ hτ hζ
  have hεk : ε ∈ cycl p k := mem_cycl_of_pow_prime_eq_one hk hεp
  have hpow : ∀ j : ℕ, (τ ^ j) ζ = ε ^ j * ζ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτζ, map_mul, ih]
      have : (τ ^ j) ε = ε := by
        clear ih
        induction j with
        | zero => simp
        | succ j ih2 => rw [pow_succ, AlgEquiv.mul_apply, hτ ε hεk, ih2]
      rw [this]; ring
  have hfix : (τ ^ p) ζ = ζ := by rw [hpow, hεp, one_mul]
  intro x hx
  rw [cycl_eq_adjoin hζ, mem_adjoin_simple_iff] at hx
  obtain ⟨r, s, rfl⟩ := hx
  rw [map_div₀, ← AlgEquiv.coe_toAlgHom, ← aeval_algHom_apply, ← aeval_algHom_apply,
    AlgEquiv.coe_toAlgHom, hfix]

theorem pow_prime_apply_ne {k : ℕ} (hk : 2 ≤ k) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hτ : ∀ x ∈ cycl p k, τ x = x) {η : PadicAlgCl p} (hη : IsPrimitiveRoot η (p ^ (k + 1)))
    (hτη : τ η ≠ η) {η' : PadicAlgCl p} (hη' : IsPrimitiveRoot η' (p ^ (k + 1 + 1))) :
    (τ ^ p) η' ≠ η' := by
  have hpr := (Fact.out : p.Prime)
  have hη'0 : η' ≠ 0 := hη'.ne_zero (pow_ne_zero _ hpr.ne_zero)
  have hη'p : IsPrimitiveRoot (η' ^ p) (p ^ (k + 1)) :=
    hη'.pow (pow_pos hpr.pos _) (by ring)
  obtain ⟨ε, hεp, hτε⟩ := exists_apply_eq_mul_of_fix τ hτ hη'p
  have hε1 : ε ≠ 1 := by
    rintro rfl; rw [one_mul] at hτε
    exact apply_ne_of_isPrimitiveRoot τ hτ hη hτη hη'p hτε
  set δ := τ η' * η'⁻¹ with hδ
  have hτη' : τ η' = δ * η' := by rw [hδ]; field_simp
  have hδp : δ ^ p = ε := by
    rw [hδ, mul_pow, inv_pow, ← map_pow, hτε, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hη'0),
      mul_one]
  have hδk : δ ∈ cycl p k := by
    apply pow_eq_one_mem_cycl
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show p ^ (j + 2) = p * (p * p ^ j) by ring, pow_mul, hδp, pow_mul, hεp, one_pow]
  have hpow : ∀ j : ℕ, (τ ^ j) η' = δ ^ j * η' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτη', map_mul, ih]
      have : (τ ^ j) δ = δ := by
        clear ih
        induction j with
        | zero => simp
        | succ j ih2 => rw [pow_succ, AlgEquiv.mul_apply, hτ δ hδk, ih2]
      rw [this]; ring
  rw [hpow, hδp]
  intro h
  have : ε = 1 := by
    have := congrArg (· * η'⁻¹) h
    simpa [mul_assoc, mul_inv_cancel₀ hη'0] using this
  exact hε1 this

theorem pow_prime_pow_fix_and_move {n : ℕ} (hn : 2 ≤ n) (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hγn : ∀ x ∈ cycl p n, γ x = x) {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    (hγζ : γ ζ ≠ ζ) (j : ℕ) :
    (∀ x ∈ cycl p (n + j), (γ ^ (p ^ j)) x = x) ∧
      ∀ η : PadicAlgCl p, IsPrimitiveRoot η (p ^ (n + j + 1)) → (γ ^ (p ^ j)) η ≠ η := by
  induction j with
  | zero =>
    simp only [pow_zero, pow_one, add_zero]
    exact ⟨hγn, fun η hη => apply_ne_of_isPrimitiveRoot γ hγn hζ hγζ hη⟩
  | succ j ih =>
    obtain ⟨hfix, hmove⟩ := ih
    have hpj : γ ^ (p ^ (j + 1)) = (γ ^ (p ^ j)) ^ p := by rw [pow_succ, pow_mul]
    obtain ⟨η, hη⟩ := exists_isPrimitiveRoot (p := p) (n + j + 1)
    refine ⟨?_, fun η' hη' => ?_⟩
    · rw [hpj, ← add_assoc]
      exact pow_prime_fix_cycl_succ (by omega) _ hfix
    · rw [hpj]
      rw [← add_assoc] at hη'
      exact pow_prime_apply_ne (by omega) _ hfix hη (hmove η hη) hη'

theorem norm_le_of_normTrace_cycl_eq_zero {n m : ℕ} (hn : 2 ≤ n)
    (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hγn : ∀ x ∈ cycl p n, γ x = x)
    {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) (hγζ : γ ζ ≠ ζ)
    {x : PadicAlgCl p} (hx : x ∈ cycl p m) (h0 : normTrace (cycl p n) x = 0) :
    ‖x‖ ≤ (p : ℝ) ^ 3 * ‖γ x - x‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rcases le_or_gt m n with hmn | hnm
  · rw [normTrace_of_mem _ (cycl_mono hmn hx)] at h0
    rw [h0, norm_zero]; positivity
  set w := γ x - x with hw
  have hwm : w ∈ cycl p m := sub_mem (map_mem_cycl γ hx) hx
  have hcomm : ∀ j y, γ (normTrace (cycl p j) y) = normTrace (cycl p j) (γ y) := fun j y =>
    (normTrace_map_of_map_eq (cycl p j) γ (cycl_map γ j) y).symm

  set f : ℕ → PadicAlgCl p := fun k => normTrace (cycl p k) x with hf
  have hlayer : ∀ k ∈ Finset.Ico n m, ‖f (k + 1) - f k‖ ≤ (p : ℝ) ^ 3 * ‖w‖ := by
    intro k hk
    obtain ⟨hnk, hkm⟩ := Finset.mem_Ico.1 hk
    have hk1 : 1 ≤ k := by omega
    set y := f (k + 1) - f k
    have hy : y ∈ cycl p (k + 1) :=
      sub_mem (normTrace_mem _ _) (cycl_mono (Nat.le_succ k) (normTrace_mem _ _))
    have hy0 : normTrace (cycl p k) y = 0 := by
      simp only [y, hf]
      rw [normTrace_sub, normTrace_normTrace_of_le (cycl_mono (p := p) (Nat.le_succ k)),
        normTrace_of_mem _ (normTrace_mem _ _), sub_self]
    have hγy : γ y - y = normTrace (cycl p (k + 1)) w - normTrace (cycl p k) w := by
      simp only [y, hf, hw, map_sub, hcomm, normTrace_sub]; ring
    have hγy' : ‖γ y - y‖ ≤ p * ‖w‖ := by
      rw [hγy, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact norm_normTrace_cycl_le (by omega) hkm hwm
      · rw [norm_neg]; exact norm_normTrace_cycl_le hk1 hkm.le hwm
    obtain ⟨hfix, hmove⟩ := pow_prime_pow_fix_and_move hn γ hγn hζ hγζ (k - n)
    rw [Nat.add_sub_cancel' hnk] at hfix hmove
    obtain ⟨η, hη⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
    have h1 := norm_le_of_normTrace_cycl_succ_eq_zero hk1 _ hfix hη (hmove η hη) hy hy0
    have h2 := norm_pow_apply_sub_le γ y (p ^ (k - n))
    calc ‖y‖ ≤ (p : ℝ) ^ 2 * ‖(γ ^ (p ^ (k - n))) y - y‖ := h1
      _ ≤ (p : ℝ) ^ 2 * (p * ‖w‖) :=
          mul_le_mul_of_nonneg_left (h2.trans hγy') (by positivity)
      _ = _ := by ring
  have htel : ∀ m' : ℕ, n ≤ m' → ∑ k ∈ Finset.Ico n m', (f (k + 1) - f k) = f m' - f n := by
    intro m' hm'
    induction m', hm' using Nat.le_induction with
    | base => simp
    | succ m' hm' ih => rw [Finset.sum_Ico_succ_top hm', ih]; ring
  have hxsum : x = ∑ k ∈ Finset.Ico n m, (f (k + 1) - f k) := by
    rw [htel m hnm.le]
    simp only [hf]
    rw [h0, sub_zero, normTrace_of_mem _ hx]
  rw [hxsum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) hlayer

end

end GroundTheory.PAdicHodge
