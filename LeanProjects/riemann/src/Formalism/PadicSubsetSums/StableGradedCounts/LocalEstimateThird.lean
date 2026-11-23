import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight
import Formalism.PadicSubsetSums.StableGradedCounts.ProdPowFactorizationLe
import Formalism.PadicSubsetSums.StableGradedCounts.FourMulSumLeProduct

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace E4

theorem geom_part (Q : ℝ) (hQ : 1 < Q) (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ ≤ (1 - (Q ^ M)⁻¹) / (Q - 1) := by
  have hQ1 : Q - 1 ≠ 0 := (sub_pos.mpr hQ).ne'
  have hQ0 : Q ≠ 0 := by positivity
  suffices h : ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ = (1 - (Q ^ M)⁻¹) / (Q - 1) from h.le
  induction M with
  | zero =>
    rw [show Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) by decide]
    simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1), ih, Nat.add_sub_cancel]
    field_simp
    ring

theorem harm_part (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹ ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
  induction M with
  | zero =>
    rw [show Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) by decide]
    simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1)]
    have h1 : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos h1 h2)
    rw [Real.log_div h1.ne' h2.ne'] at hlog
    have hab : ((m + 1 : ℕ) : ℝ) = ((m + 1 + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
    have hdiv : ((m + 1 : ℕ) : ℝ) / ((m + 1 + 1 : ℕ) : ℝ) = 1 - (((m + 1 + 1 : ℕ) : ℝ))⁻¹ := by
      rw [hab, sub_div, div_self h2.ne', one_div]
    linarith

theorem term_le (q δ b : ℕ) (hq : 2 ≤ q) (hδ : 2 ≤ δ)
    (h : δ * b ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    (b : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤ ((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹ := by
  have hq1 : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hB : (0:ℝ) < (q:ℝ) - 1 := by linarith
  have hD : (0:ℝ) < δ := by exact_mod_cast (by omega : 0 < δ)
  have hP1 : (1:ℝ) ≤ (q:ℝ) ^ (δ - 1) := one_le_pow₀ hq1.le
  have hP0 : (q:ℝ) ^ (δ - 1) ≠ 0 := by positivity
  have hpow : (q:ℝ) ^ δ = (q:ℝ) * (q:ℝ) ^ (δ - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hA : (0:ℝ) < (q:ℝ) ^ δ - 1 := by nlinarith
  have hcast : ((q ^ δ - 1 : ℕ) : ℝ) = (q:ℝ) ^ δ - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hcast2 : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hR : (δ:ℝ) * b ≤ δ * ((q:ℝ) - 1) + ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) := by
    have h' : ((δ * b : ℕ) : ℝ) ≤ ((δ * (q - 1) + (q ^ δ - 1) / (q - 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr h
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hcast2] at h'
    have h'' : (((q ^ δ - 1) / (q - 1) : ℕ) : ℝ) ≤ ((q ^ δ - 1 : ℕ) : ℝ) / ((q - 1 : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [hcast, hcast2] at h''
    linarith
  have hstep : (b:ℝ) ≤ ((q:ℝ) - 1) + ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) / δ := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hD]
    nlinarith
  have e1 : ((q:ℝ) ^ (δ - 1))⁻¹ * ((q:ℝ) ^ δ - 1) = (q:ℝ) - ((q:ℝ) ^ (δ - 1))⁻¹ := by
    rw [hpow, mul_comm (q:ℝ) ((q:ℝ) ^ (δ - 1)), mul_sub, inv_mul_cancel_left₀ hP0, mul_one]
  have e2 : ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹ * ((q:ℝ) ^ δ - 1) =
      ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) / δ := by
    ring
  have hPinv : ((q:ℝ) ^ (δ - 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP1
  have key : (b:ℝ) ≤ (((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹) * ((q:ℝ) ^ δ - 1) := by
    rw [add_mul, e1, e2]
    linarith
  calc (b:ℝ) * ((q:ℝ) ^ δ - 1)⁻¹
      ≤ ((((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹) * ((q:ℝ) ^ δ - 1)) *
          ((q:ℝ) ^ δ - 1)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hA.le)
    _ = ((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹ := mul_inv_cancel_right₀ hA.ne' _

theorem arith (q N : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (b : ℕ → ℕ) (m : ℝ)
    (h1 : (b 1 : ℝ) * ((q : ℝ) - 1)⁻¹ ≤ m)
    (h2 : ∀ δ, 2 ≤ δ → δ * b δ ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    ∑ δ ∈ Finset.Icc 1 N, (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      m + (1 + Real.log N) / ((q : ℝ) - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hQ : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hQ1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ M + 1)]
  have hI : Finset.Ioc 1 (M + 1) = Finset.Icc 2 (M + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hI, pow_one]
  have h3 : ∑ δ ∈ Finset.Icc 2 (M + 1), (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      ∑ δ ∈ Finset.Icc 2 (M + 1), (((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹) :=
    Finset.sum_le_sum fun δ hδ =>
      term_le q δ (b δ) hq (Finset.mem_Icc.1 hδ).1 (h2 δ (Finset.mem_Icc.1 hδ).1)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h3
  have h4 := geom_part (q : ℝ) hQ M
  have h5 := harm_part M
  have h6 : (1 - ((q : ℝ) ^ M)⁻¹) / ((q : ℝ) - 1) ≤ 1 / ((q : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ hQ1.le
    have : 0 ≤ ((q : ℝ) ^ M)⁻¹ := by positivity
    linarith
  have h7 : (∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹) * ((q : ℝ) - 1)⁻¹ ≤
      Real.log ((M + 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right h5 (inv_nonneg.2 hQ1.le)
  have h8 : (1 + Real.log ((M + 1 : ℕ) : ℝ)) / ((q : ℝ) - 1) =
      1 / ((q : ℝ) - 1) + Real.log ((M + 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ := by
    rw [add_div, div_eq_mul_inv (Real.log _)]
  rw [h8]
  linarith

theorem exists_prime_pow_eq {M : Type} [Monoid M] (n : ℕ) (hn : 2 ≤ n) (u : M) (hu : u ^ n = 1)
    (l a : ℕ) (hl : l.Prime) (hla : u ^ (l ^ a) = 1) :
    ∃ l' ∈ n.primeFactors, u ^ (l' ^ padicValNat l' n) = 1 := by
  have hd1 : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one hu
  have hd2 : orderOf u ∣ l ^ a := orderOf_dvd_of_pow_eq_one hla
  obtain ⟨k, _, hk'⟩ := (Nat.dvd_prime_pow hl).mp hd2
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero, orderOf_eq_one_iff] at hk'
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩, by rw [hk', one_pow]⟩
  · have hln : l ^ k ∣ n := by
      rw [← hk']
      exact hd1
    have hl_n : l ∣ n := (dvd_pow_self l hpos.ne').trans hln
    refine ⟨l, Nat.mem_primeFactors.mpr ⟨hl, hl_n, by omega⟩, ?_⟩
    rw [← orderOf_dvd_iff_pow_eq_one, hk']
    apply pow_dvd_pow
    haveI := Fact.mk hl
    exact (padicValNat_dvd_iff_le (by omega)).mp hln

variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]

theorem key (P : K[X]) (hP : Irreducible P) (hm : P.Monic) (x : L) (hx : aeval x P = 0)
    (hx0 : x ≠ 0) (c₀ : Kˣ) (l : ℕ) (hl : l.Prime)
    (h : primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))) (hq : 3 ≤ Fintype.card K) :
    ∃ l' ∈ (Fintype.card K ^ P.natDegree - 1).primeFactors,
      P ∣ X ^ (l' ^ padicValNat l' (Fintype.card K ^ P.natDegree - 1)) -
        C ((c₀ : K) ^ (l' ^ padicValNat l' (Fintype.card K ^ P.natDegree - 1))) := by
  classical
  set q := Fintype.card K with hqdef
  set d := P.natDegree with hd
  set n := q ^ d - 1 with hn
  have hint : IsIntegral K x := ⟨P, hm, by rwa [Polynomial.aeval_def] at hx⟩
  have hmin : P = minpoly K x := minpoly.eq_of_irreducible_of_monic hP hx hm
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hP)
  have hqd : 3 ≤ q ^ d := le_trans hq (Nat.le_self_pow (by omega) q)
  have hn2 : 2 ≤ n := by omega
  have hxn : x ^ n = 1 := by
    haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
    letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _
    have hcard : Fintype.card (IntermediateField.adjoin K {x}) = q ^ d := by
      rw [Module.card_eq_pow_finrank (K := K), IntermediateField.adjoin.finrank hint, ← hmin]
    have hxE : (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x}) ≠ 0 := by
      intro h0
      exact hx0 (congrArg Subtype.val h0)
    have h1 := FiniteField.pow_card_sub_one_eq_one _ hxE
    rw [hcard] at h1
    have h2 := congrArg (fun e : IntermediateField.adjoin K {x} => (e : L)) h1
    simpa using h2
  have hc0 : (c₀ : K) ≠ 0 := c₀.ne_zero
  have hcK : (c₀ : K) ^ n = 1 := by
    have h1 := FiniteField.pow_card_pow d (c₀ : K)
    have h2 : (c₀ : K) ^ n * (c₀ : K) = (c₀ : K) := by
      rw [← pow_succ, hn, Nat.sub_add_cancel (by omega : 1 ≤ q ^ d)]
      exact h1
    exact mul_right_cancel₀ hc0 (h2.trans (one_mul _).symm)
  have hcL : algebraMap K L (c₀ : K) ≠ 0 := (_root_.map_ne_zero _).mpr hc0
  have hcn : algebraMap K L (c₀ : K) ^ n = 1 := by rw [← map_pow, hcK, map_one]
  have aux : ∀ z : L, z ≠ 0 → z ^ n = 1 →
      ∃ E : ℕ, (z / Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart l z) ^ (l ^ E) = 1 := by
    intro z hz0 hzn
    have ho : 0 < orderOf z :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, by omega, hzn⟩)
    have key2 : ∀ a b : ℕ, a ≡ b [MOD orderOf z] → z ^ a = z ^ b := fun a b hab => by
      rw [← pow_mod_orderOf z a, ← pow_mod_orderOf z b]
      exact congrArg (fun k => z ^ k) hab
    refine ⟨(orderOf z).factorization l, ?_⟩
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart.eq_1]
    have hcop : (l ^ (orderOf z).factorization l).Coprime
        (orderOf z / l ^ (orderOf z).factorization l) :=
      (Nat.coprime_ordCompl hl ho.ne').pow_left _
    have hmod := (Nat.ModEq.pow_totient hcop).mul_right' (l ^ (orderOf z).factorization l)
    rw [one_mul, Nat.div_mul_cancel (Nat.ordProj_dvd (orderOf z) l)] at hmod
    rw [div_pow, ← pow_mul z, key2 _ _ hmod, div_self (pow_ne_zero _ hz0)]
  obtain ⟨E1, hE1⟩ := aux x hx0 hxn
  obtain ⟨E2, hE2⟩ := aux _ hcL hcn
  rw [h] at hE1
  have hp0 : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart l (algebraMap K L (c₀ : K)) ≠ 0 := by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart.eq_1]
    exact pow_ne_zero _ hcL
  have hyE : (x / algebraMap K L (c₀ : K)) ^ (l ^ (E1 + E2)) = 1 := by
    rw [← div_div_div_cancel_right₀ hp0 x (algebraMap K L (c₀ : K)), div_pow, pow_add,
      pow_mul (x / _), hE1, one_pow, mul_comm (l ^ E1), pow_mul, hE2, one_pow, div_one]
  have hyn : (x / algebraMap K L (c₀ : K)) ^ n = 1 := by
    rw [div_pow, hxn, hcn, div_one]
  obtain ⟨l', hl', hyl'⟩ := exists_prime_pow_eq n hn2 (x / algebraMap K L (c₀ : K)) hyn l (E1 + E2) hl hyE
  refine ⟨l', hl', ?_⟩
  have hdiv := minpoly.dvd K x (p := (X ^ (l' ^ padicValNat l' n) -
    C ((c₀ : K) ^ (l' ^ padicValNat l' n)) : K[X])) ?_
  · rwa [← hmin] at hdiv
  · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_pow, sub_eq_zero]
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hcL)] at hyl'
    exact hyl'

open Classical in

noncomputable def Bset (K : Type) [Field K] [Fintype K] (δ : ℕ) (c₀ : Kˣ) : Finset (Fin δ → K) :=
  Finset.univ.filter (fun c => Irreducible (monicOf c) ∧
    ∃ l' ∈ (Fintype.card K ^ δ - 1).primeFactors,
      monicOf c ∣ X ^ (l' ^ padicValNat l' (Fintype.card K ^ δ - 1)) -
        C ((c₀ : K) ^ (l' ^ padicValNat l' (Fintype.card K ^ δ - 1))))

theorem count (δ : ℕ) (c₀ : Kˣ) :
    δ * (Bset K δ c₀).card ≤
      ∑ l ∈ (Fintype.card K ^ δ - 1).primeFactors, l ^ padicValNat l (Fintype.card K ^ δ - 1) := by
  classical
  have hmon : ∀ c : Fin δ → K, (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).Monic := fun c => by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hdegc : ∀ c : Fin δ → K, (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).natDegree = δ := fun c => by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1, Polynomial.natDegree_add_eq_left_of_degree_lt,
      Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt _
  have hcoeff : ∀ (c : Fin δ → K) (j : Fin δ), (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).coeff j = c j := by
    intro c j
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.finset_sum_coeff]
    simp [Polynomial.coeff_C_mul_X_pow, Fin.val_inj, j.isLt.ne]
  have hinj : Function.Injective (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf : (Fin δ → K) → K[X]) :=
    fun c c' h => funext fun j => by rw [← hcoeff c j, ← hcoeff c' j, h]
  have hgen : ∀ (k : ℕ) (a : K), 0 < k → δ * (Finset.univ.filter (fun c : Fin δ → K =>
      Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a)).card ≤ k := by
    intro k a hk
    have hF0 : (X ^ k - C a : K[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hk a
    have hprod : ∏ c ∈ Finset.univ.filter (fun c : Fin δ → K =>
        Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a),
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a := by
      apply Finset.prod_dvd_of_coprime
      · intro c hc c' hc' hne
        have hi := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2.1
        have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2.1
        show IsCoprime (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c')
        rw [hi.coprime_iff_not_dvd]
        intro hdvd
        apply hne
        apply hinj
        exact Polynomial.eq_of_monic_of_associated (hmon c) (hmon c') (hi.associated_of_dvd hi' hdvd)
      · intro c hc
        exact (Finset.mem_filter.mp hc).2.2
    have hdeg := Polynomial.natDegree_le_of_dvd hprod hF0
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => hmon c),
      Polynomial.natDegree_X_pow_sub_C] at hdeg
    simp only [hdegc, Finset.sum_const, smul_eq_mul] at hdeg
    rw [mul_comm]
    exact hdeg
  set m := Fintype.card K ^ δ - 1 with hmdef
  have hsub : Bset K δ c₀ ⊆ m.primeFactors.biUnion (fun l' => Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))) := by
    intro c hc
    simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hirr, l', hl', hdvd⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨l', hl', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hirr, hdvd⟩⟩
  calc δ * (Bset K δ c₀).card
      ≤ δ * (m.primeFactors.biUnion (fun l' => Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m))))).card :=
        Nat.mul_le_mul le_rfl (Finset.card_le_card hsub)
    _ ≤ δ * ∑ l' ∈ m.primeFactors, (Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))).card :=
        Nat.mul_le_mul le_rfl Finset.card_biUnion_le
    _ = ∑ l' ∈ m.primeFactors, δ * (Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))).card := by
        rw [Finset.mul_sum]
    _ ≤ ∑ l' ∈ m.primeFactors, l' ^ padicValNat l' m := by
        apply Finset.sum_le_sum
        intro l' hl'
        exact hgen _ _ (pow_pos (Nat.prime_of_mem_primeFactors hl').pos _)

theorem sqWeight_irred (P : K[X]) (hP : Irreducible P) (hm : P.Monic) :
    sqWeight P = ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹ := by
  classical
  rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight.eq_1, UniqueFactorizationMonoid.normalizedFactors_irreducible hP,
    hm.normalize_eq_self]
  simp

theorem weight_le (N : ℕ) (c₀ : Kˣ) (hq : 3 ≤ Fintype.card K) :
    wtOf (fun c : Fin N → K => sqWeight (monicOf c)) {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
        l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} ≤
      ∑ δ ∈ Finset.Icc 1 N, ((Bset K δ c₀).card : ℝ) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
  classical
  set μ : (Fin N → K) → ℝ := fun c => sqWeight (monicOf c) with hμ
  have hμ0 : ∀ c, 0 ≤ μ c := fun c => sqWeight_nonneg _
  have hsub : {c : Fin N → K | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
        l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} ⊆
      ⋃ δ ∈ Finset.Icc 1 N, ⋃ c' ∈ Bset K δ c₀,
        {c : Fin N → K | c ∈ sqSet K N ∧ monicOf c' ∣ monicOf c} := by
    rintro c ⟨hc, l, hl, -, x, hx, hpt⟩
    have hfx : aeval x (monicOf c) = 0 := (mem_rootSet.1 hx).2
    have hint : IsIntegral K x := ⟨monicOf c, monicOf_monic c, hfx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply ((mem_sqSet c).1 hc).2
      have : aeval (0 : L) (monicOf c) = algebraMap K L ((monicOf c).coeff 0) := by
        rw [aeval_def, eval₂_at_zero]
      rw [this, map_eq_zero] at hfx
      exact hfx
    set P := minpoly K x with hPdef
    have hPi : Irreducible P := minpoly.irreducible hint
    have hPm : P.Monic := minpoly.monic hint
    have hPd : P ∣ monicOf c := minpoly.dvd K x hfx
    have hdeg : P.natDegree ≤ N := by
      have := natDegree_le_of_dvd hPd (monicOf_monic c).ne_zero
      rwa [monicOf_natDegree] at this
    obtain ⟨l', hl', hdv⟩ := key P hPi hPm x (minpoly.aeval K x) hx0 c₀ l hl hpt hq
    have hco : monicOf (fun i : Fin P.natDegree => P.coeff i) = P := monicOf_coeffs hPm rfl
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨P.natDegree, Finset.mem_Icc.2 ⟨hPi.natDegree_pos, hdeg⟩,
      fun i : Fin P.natDegree => P.coeff i, ?_, hc, by rw [hco]; exact hPd⟩
    unfold Bset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hco]
    exact ⟨hPi, l', hl', hdv⟩
  refine (wtOf_mono μ hμ0 hsub).trans ((wtOf_biUnion_le μ hμ0 _ _).trans ?_)
  refine Finset.sum_le_sum fun δ hδ => ?_
  refine (wtOf_biUnion_le μ hμ0 _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun c' hc' => ?_
  have hi : Irreducible (monicOf c') := (Finset.mem_filter.mp hc').2.1
  rw [wtOf_eq_filter']
  have := divisor_square_weight_sum_le square_mass_le_one K N (monicOf c') (monicOf_monic c')
    (by rw [monicOf_natDegree]; exact (Finset.mem_Icc.1 hδ).2)
    ((sqSet K N).filter (fun c => monicOf c' ∣ monicOf c))
    (fun c hc => by simpa only [Finset.mem_filter] using hc)
  rw [sqWeight_irred _ hi (monicOf_monic c'), monicOf_natDegree] at this
  exact this

end E4

theorem local_estimate_third : LocalEstimateIII := by
  classical
  intro K L _ _ _ _ _ N q₁ d c₀ hN hq1 hd hne h12 hd2 hmax h16 hq1d hdd
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq17 : 17 ≤ Fintype.card K := by
    have := Nat.le_of_dvd (by omega) h16
    omega
  have hw := E4.weight_le (L := L) N c₀ (by omega)
  rw [wtOf_eq_filter'] at hw
  have c1 : ((Fintype.card K - 1 : ℕ) : ℝ) = (Fintype.card K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1 : (((E4.Bset K 1 c₀).card : ℕ) : ℝ) * ((Fintype.card K : ℝ) - 1)⁻¹ ≤
      1 / (4 * (min q₁ d : ℕ)) := by
    have hc := E4.count 1 c₀
    rw [one_mul, pow_one] at hc
    have hs := prime_power_order_share (Fintype.card K) q₁ d hq2 hq1 hd hne h12 hd2 hmax h16
      hq1d hdd
    refine le_trans ?_ hs
    rw [c1, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hc
    · apply inv_nonneg.2
      have : (17 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast hq17
      linarith
  have h2 : ∀ δ, 2 ≤ δ → δ * (E4.Bset K δ c₀).card ≤
      δ * (Fintype.card K - 1) + (Fintype.card K ^ δ - 1) / (Fintype.card K - 1) := fun δ hδ =>
    (E4.count δ c₀).trans (prime_power_order_count (Fintype.card K) δ hq2
      (dvd_trans (by norm_num) h16) (by omega))
  have ha := E4.arith (Fintype.card K) N hN hq2 (fun δ => (E4.Bset K δ c₀).card) _ h1 h2
  exact hw.trans ha

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
