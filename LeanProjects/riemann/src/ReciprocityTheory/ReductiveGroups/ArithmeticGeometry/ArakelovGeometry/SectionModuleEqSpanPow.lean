import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}

private theorem section_module_eq_span_pow (x : κ → Ω) (n : ℕ) :
    sec ℤ x n = (Submodule.span ℤ (Set.range x)) ^ n := by
  unfold sec
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp]
  congr 2
  ext i
  simp

theorem sec_mul_sec (x : κ → Ω) (a b : ℕ) : sec ℤ x a * sec ℤ x b = sec ℤ x (a + b) := by
  rw [section_module_eq_span_pow, section_module_eq_span_pow, section_module_eq_span_pow, pow_add]

theorem sec_eq_span_pow (x : κ → Ω) (n : ℕ) :
    sec ℤ x n = (Submodule.span ℤ (Set.range x)) ^ n :=
  section_module_eq_span_pow x n

theorem sec_comp_le (x : κ → Ω) (e : Fin (D + 1) → κ) (n : ℕ) : sec ℤ (x ∘ e) n ≤ sec ℤ x n := by
  rintro z ⟨p, hp, rfl⟩
  refine ⟨MvPolynomial.rename e p, hp.rename_isHomogeneous, ?_⟩
  simp [MvPolynomial.aeval_rename]

theorem sec_fg (x : κ → Ω) (n : ℕ) : (sec ℤ x n).FG :=
  (MvPolynomial.homogeneousSubmodule_fg κ ℤ n).map _

private theorem coneMap_monomial_one (y : κ → Ω) (s : κ →₀ ℕ) :
    coneMap ℤ y (MvPolynomial.monomial s (1 : ℤ)) =
      C (MvPolynomial.aeval y (MvPolynomial.monomial s (1 : ℤ))) * X ^ s.degree := by
  induction s using Finsupp.induction with
  | zero => simp [coneMap]
  | single_add a b f _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, ih, map_add, Finsupp.degree_single]
    simp only [coneMap, map_mul, map_pow, MvPolynomial.aeval_X, pow_add, mul_pow]
    ring

private theorem coneMap_of_isHomogeneous (y : κ → Ω) {p : MvPolynomial κ ℤ} {n : ℕ}
    (hp : p.IsHomogeneous n) : coneMap ℤ y p = C (MvPolynomial.aeval y p) * X ^ n := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    have := hp (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  rw [show MvPolynomial.monomial d (p.coeff d) = (p.coeff d) • MvPolynomial.monomial d (1 : ℤ) by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, map_smul, coneMap_monomial_one, hdeg, ← smul_mul_assoc, Polynomial.smul_C]

private theorem coeff_coneMap_mem (y : κ → Ω) (p : MvPolynomial κ ℤ) (N : ℕ) :
    (coneMap ℤ y p).coeff N ∈ sec ℤ y N := by
  rw [← MvPolynomial.sum_homogeneousComponent p, map_sum, Polynomial.finsetSum_coeff]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [coneMap_of_isHomogeneous y (MvPolynomial.homogeneousComponent_isHomogeneous k p),
    Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · subst h
    exact ⟨_, MvPolynomial.homogeneousComponent_isHomogeneous _ p, rfl⟩
  · exact zero_mem _

private theorem pow_mem_sec (x : κ → Ω) (i : κ) (j : ℕ) : x i ^ j ∈ sec ℤ x j := by
  rw [sec_eq_span_pow]
  exact Submodule.pow_mem_pow _ (Submodule.subset_span (Set.mem_range_self i)) j

private theorem exists_pow_mem (x : κ → Ω) (e : Fin (D + 1) → κ) (i : κ)
    (hi : IsIntegral (coneRing ℤ (x ∘ e)) (C (x i) * X : Polynomial Ω)) :
    ∃ N : ℕ, x i ^ N ∈ ⨆ (j : ℕ) (_ : j < N), sec ℤ (x ∘ e) (N - j) * sec ℤ x j := by
  obtain ⟨p, hpm, hp⟩ := hi
  set N := p.natDegree
  refine ⟨N, ?_⟩
  have key : ∀ a : coneRing ℤ (x ∘ e), ∀ j < N,
      (algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω) a * (C (x i) * X) ^ j).coeff N ∈
        sec ℤ (x ∘ e) (N - j) * sec ℤ x j := by
    intro a j hj
    obtain ⟨q, hq⟩ := a.2
    show ((a : Polynomial Ω) * (C (x i) * X) ^ j).coeff N ∈ _
    rw [mul_pow, ← C_pow, ← mul_assoc, coeff_mul_X_pow', if_pos hj.le, coeff_mul_C, ← hq]
    exact Submodule.mul_mem_mul (coeff_coneMap_mem _ q _) (pow_mem_sec x i j)
  have h1 : (eval₂ (algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω)) (C (x i) * X) p).coeff N = 0 := by
    rw [hp]; simp
  rw [hpm.as_sum, eval₂_add, eval₂_X_pow, eval₂_finsetSum, coeff_add, finsetSum_coeff] at h1
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow] at h1
  rw [mul_pow, ← C_pow, coeff_C_mul_X_pow, if_pos rfl] at h1
  rw [eq_neg_of_add_eq_zero_left h1]
  refine neg_mem (Submodule.sum_mem _ fun j hj => ?_)
  have hj' : j < N := Finset.mem_range.mp hj
  exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj' (key _ j hj'))

private theorem one_le_sec_zero (x : κ → Ω) : (1 : Submodule ℤ Ω) ≤ sec ℤ x 0 := by
  rw [sec_eq_span_pow, pow_zero]

private theorem monomial_mem_sec (x : κ → Ω) (d : κ →₀ ℕ) :
    MvPolynomial.aeval x (MvPolynomial.monomial d (1 : ℤ)) ∈ sec ℤ x d.degree :=
  ⟨_, MvPolynomial.isHomogeneous_monomial _ rfl, rfl⟩

private theorem sec_le_of_monomial (x : κ → Ω) (n : ℕ) (P : Submodule ℤ Ω)
    (h : ∀ d : κ →₀ ℕ, d.degree = n → MvPolynomial.aeval x (MvPolynomial.monomial d (1 : ℤ)) ∈ P) :
    sec ℤ x n ≤ P := by
  rintro z ⟨p, hp, rfl⟩
  show MvPolynomial.aeval x p ∈ P
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]; exact hp (MvPolynomial.mem_support_iff.mp hd)
  rw [show MvPolynomial.monomial d (p.coeff d) = (p.coeff d) • MvPolynomial.monomial d (1 : ℤ) by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
  exact Submodule.smul_mem _ _ (h d hdeg)

private theorem exists_le_of_sum_lt (N : κ → ℕ) (d : κ →₀ ℕ) (hd : ∑ i, (N i - 1) < d.degree) :
    ∃ i, N i ≤ d i := by
  by_contra hc
  push Not at hc
  have : d.degree ≤ ∑ i, (N i - 1) := by
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun i _ => by have := hc i; omega
  omega

private theorem mul_iSup_sec_le (x : κ → Ω) (e : Fin (D + 1) → κ) (K a b n : ℕ) (hab : a + b = n) :
    sec ℤ (x ∘ e) a * (⨆ (j : ℕ) (_ : j ≤ b ∧ j ≤ K), sec ℤ (x ∘ e) (b - j) * sec ℤ x j) ≤
      ⨆ (j : ℕ) (_ : j ≤ n ∧ j ≤ K), sec ℤ (x ∘ e) (n - j) * sec ℤ x j := by
  rw [Submodule.mul_iSup]
  refine iSup_le fun j => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun hj => ?_
  refine le_iSup₂_of_le j ⟨by omega, hj.2⟩ ?_
  rw [← mul_assoc, sec_mul_sec, show a + (b - j) = n - j by omega]

private theorem sec_le_iSup (x : κ → Ω) (e : Fin (D + 1) → κ) (N : κ → ℕ)
    (hN : ∀ i, x i ^ N i ∈ ⨆ (j : ℕ) (_ : j < N i), sec ℤ (x ∘ e) (N i - j) * sec ℤ x j)
    (K : ℕ) (hK : ∀ d : κ →₀ ℕ, K < d.degree → ∃ i, N i ≤ d i) (n : ℕ) :
    sec ℤ x n ≤ ⨆ (j : ℕ) (_ : j ≤ n ∧ j ≤ K), sec ℤ (x ∘ e) (n - j) * sec ℤ x j := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hn : n ≤ K
  · refine le_trans ?_ (le_iSup₂_of_le n ⟨le_rfl, hn⟩ le_rfl)
    rw [Nat.sub_self]
    calc sec ℤ x n = 1 * sec ℤ x n := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (one_le_sec_zero _) le_rfl
  · push Not at hn
    apply sec_le_of_monomial
    intro d hd
    obtain ⟨i, hi⟩ := hK d (hd ▸ hn)
    set d' := d - Finsupp.single i (N i)
    have hdd : d = d' + Finsupp.single i (N i) :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)).symm
    have hdeg' : d'.degree + N i = n := by rw [← hd, hdd, map_add, Finsupp.degree_single]
    have hm : MvPolynomial.monomial (d' + Finsupp.single i (N i)) (1 : ℤ) =
        MvPolynomial.monomial d' 1 * MvPolynomial.X i ^ N i := by
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]
    rw [hdd, hm, map_mul, map_pow, MvPolynomial.aeval_X]
    have hmem := Submodule.mul_mem_mul (monomial_mem_sec x d') (hN i)
    refine (?_ : sec ℤ x d'.degree * _ ≤ _) hmem
    rw [Submodule.mul_iSup]; refine iSup_le fun j => ?_
    rw [Submodule.mul_iSup]; refine iSup_le fun hj => ?_
    calc sec ℤ x d'.degree * (sec ℤ (x ∘ e) (N i - j) * sec ℤ x j)
        = sec ℤ (x ∘ e) (N i - j) * sec ℤ x (d'.degree + j) := by
          rw [mul_left_comm, sec_mul_sec]
      _ ≤ sec ℤ (x ∘ e) (N i - j) * ⨆ (j' : ℕ) (_ : j' ≤ d'.degree + j ∧ j' ≤ K),
            sec ℤ (x ∘ e) (d'.degree + j - j') * sec ℤ x j' :=
          mul_le_mul' le_rfl (ih _ (by omega))
      _ ≤ _ := mul_iSup_sec_le x e K _ _ n (by omega)

private theorem finrank_homog (n : ℕ) :
    finrank ℤ (MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) = (n + D).choose D := by
  have hs : {d : Fin (D + 1) →₀ ℕ | d.degree = n} =
      ((Finset.univ.finsuppAntidiag n : Finset (Fin (D + 1) →₀ ℕ)) : Set (Fin (D + 1) →₀ ℕ)) := by
    ext d; simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hs,
    (AddMonoidAlgebra.supportedEquivFinsupp _).finrank_eq, Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show D + 1 + n - 1 = n + D by omega]
  exact Nat.choose_symm_add

theorem exists_sec_eq_mul (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    ∃ k₀ : ℕ, ∀ n, k₀ ≤ n → sec ℤ x n = sec ℤ (x ∘ e) (n - k₀) * sec ℤ x k₀ := by
  choose N hN using fun i => exists_pow_mem x e i (h.integral i)
  refine ⟨∑ i, (N i - 1), fun n hn => le_antisymm ?_ ?_⟩
  · refine (sec_le_iSup x e N hN _ (exists_le_of_sum_lt N) n).trans (iSup₂_le fun j hj => ?_)
    set K := ∑ i, (N i - 1)
    calc sec ℤ (x ∘ e) (n - j) * sec ℤ x j
        = sec ℤ (x ∘ e) (n - K) * (sec ℤ (x ∘ e) (K - j) * sec ℤ x j) := by
          rw [← mul_assoc, sec_mul_sec, show n - K + (K - j) = n - j by omega]
      _ ≤ sec ℤ (x ∘ e) (n - K) * sec ℤ x K := by
          refine mul_le_mul' le_rfl ?_
          calc sec ℤ (x ∘ e) (K - j) * sec ℤ x j ≤ sec ℤ x (K - j) * sec ℤ x j :=
                mul_le_mul' (sec_comp_le x e _) le_rfl
            _ = sec ℤ x K := by rw [sec_mul_sec, Nat.sub_add_cancel hj.2]
  · calc sec ℤ (x ∘ e) (n - ∑ i, (N i - 1)) * sec ℤ x (∑ i, (N i - 1))
        ≤ sec ℤ x (n - ∑ i, (N i - 1)) * sec ℤ x (∑ i, (N i - 1)) :=
          mul_le_mul' (sec_comp_le x e _) le_rfl
      _ = sec ℤ x n := by rw [sec_mul_sec, Nat.sub_add_cancel hn]

theorem finrank_sec_free (y : Fin (D + 1) → Ω) (hy : coordIdeal ℤ y = ⊥) (n : ℕ) :
    finrank ℤ (sec ℤ y n) = (n + D).choose D := by
  set H := MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n
  set f := ((MvPolynomial.aeval y : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Ω).toLinearMap).domRestrict H
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun p hp => ?_
    have hp' : MvPolynomial.aeval y (p : MvPolynomial (Fin (D + 1)) ℤ) = 0 := hp
    have hmem : (p : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
      rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous y p.2, hp']
      simp
    rw [hy, Ideal.mem_bot] at hmem
    exact Subtype.ext hmem
  have hr : LinearMap.range f = sec ℤ y n := LinearMap.range_domRestrict _ _
  rw [← finrank_homog (D := D) n, ← hr]
  exact (LinearEquiv.ofInjective f hinj).finrank_eq.symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
