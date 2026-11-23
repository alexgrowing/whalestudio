import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

variable {R : Type} [CommRing R]

theorem psTrunc_eq {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) :
    psTrunc m f = MvPowerSeries.truncTotal (m + 1) f := by
  ext e
  have hle : ∀ i, e i ≤ e.degree := fun i => by
    first
    | exact Finsupp.le_degree i e
    | exact Finsupp.le_degree e i
    | (by_cases hi : e i = 0
       · omega
       · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
           (Finsupp.mem_support_iff.2 hi))
  have hdeg : (e.sum fun _ k => k) = e.degree := by
    first
    | rfl
    | simp [Finsupp.degree, Finsupp.sum]
  have hmem : e ∈ degLE m ↔ e.degree < m + 1 := by
    unfold degLE
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      omega
    · intro h
      refine ⟨⟨fun i => ⟨e i, by have := hle i; omega⟩, ?_⟩, by omega⟩
      ext i
      simp
  have hL : MvPolynomial.coeff e (psTrunc m f) =
      if e ∈ degLE m then MvPowerSeries.coeff e f else 0 := by
    unfold psTrunc
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    first
    | exact Finset.sum_ite_eq' (degLE m) e (fun x => MvPowerSeries.coeff x f)
    | exact Finset.sum_ite_eq (degLE m) e (fun x => MvPowerSeries.coeff x f)
    | simp
  rw [hL]
  by_cases h : e.degree < m + 1
  · rw [if_pos (hmem.2 h), MvPowerSeries.coeff_truncTotal]
    exact h
  · rw [if_neg (fun h' => h (hmem.1 h'))]
    first
    | exact (MvPowerSeries.coeff_truncTotal_eq_zero (by omega)).symm
    | exact (MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)).symm
    | (rw [MvPowerSeries.coeff_truncTotal_eq_zero]; omega)
    | exact (MvPowerSeries.coeff_truncTotal_of_le (by omega)).symm
    | simp [MvPowerSeries.truncTotal, MvPowerSeries.truncTotalFun, MvPolynomial.coeff_sum, h]
    | (simp [MvPowerSeries.truncTotal, h]; done)

private lemma mem_orig_pow_lemma_6 {ι : Type} (m : ℕ) (Q : MvPolynomial ι R)
    (hQ : ∀ e : ι →₀ ℕ, e.degree < m + 1 → MvPolynomial.coeff e Q = 0) :
    Q ∈ orig R ι ^ (m + 1) := by
  rw [Q.as_sum]
  refine Ideal.sum_mem _ fun e he => ?_
  have hd : m + 1 ≤ e.degree := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 he) (hQ e (by omega))
  rw [MvPolynomial.monomial_eq]
  refine Ideal.mul_mem_left _ _ ?_
  refine Ideal.pow_le_pow_right hd ?_
  have hX : ∀ i, (MvPolynomial.X i : MvPolynomial ι R) ∈ orig R ι := fun i => by
    first
    | exact Ideal.subset_span ⟨i, rfl⟩
    | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩)
  have h1 : (∏ i ∈ e.support, (MvPolynomial.X i : MvPolynomial ι R) ^ e i) ∈
      ∏ i ∈ e.support, orig R ι ^ e i :=
    Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hX i) _
  rw [Finset.prod_pow_eq_pow_sum] at h1
  first
  | exact h1
  | (unfold Finsupp.prod; simpa [Finsupp.degree] using h1)

theorem mk_trunc_coe {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (P : MvPolynomial ι R) :
    (Ideal.Quotient.mk (orig R ι ^ (m + 1))
      (MvPowerSeries.truncTotal (m + 1) (P : MvPowerSeries ι R))) = Ideal.Quotient.mk _ P := by
  rw [Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_6
  intro e he
  first
  | (rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal, MvPolynomial.coeff_coe,
      sub_self] <;> exact he)
  | simp [MvPowerSeries.coeff_truncTotal, he]

private lemma coe_sub_lemma_7 {ι : Type} (x y : MvPolynomial ι R) :
    ((x - y : MvPolynomial ι R) : MvPowerSeries ι R) = (x : MvPowerSeries ι R) - y := by
  rw [eq_sub_iff_add_eq, ← MvPolynomial.coe_add, sub_add_cancel]

private lemma low_mul_lemma {τ : Type} {F G : MvPowerSeries τ R} {p q : ℕ}
    (hF : ∀ e : τ →₀ ℕ, e.degree < p → MvPowerSeries.coeff e F = 0)
    (hG : ∀ e : τ →₀ ℕ, e.degree < q → MvPowerSeries.coeff e G = 0) :
    ∀ e : τ →₀ ℕ, e.degree < p + q → MvPowerSeries.coeff e (F * G) = 0 := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  replace hx : x.1 + x.2 = e := by
    first
    | exact Finset.mem_antidiagonal.1 hx
    | simpa using hx
    | exact Finsupp.mem_antidiagonal.1 hx
  have hd : x.1.degree + x.2.degree = e.degree := by
    rw [← hx]
    first
    | exact (map_add Finsupp.degree x.1 x.2).symm
    | exact (Finsupp.degree_add x.1 x.2).symm
    | simp [Finsupp.degree, Finsupp.sum_add_index']
    | (simp only [Finsupp.degree_eq_weight_one, map_add])
  by_cases h1 : x.1.degree < p
  · rw [hF _ h1, zero_mul]
  · rw [hG _ (by omega), mul_zero]

private lemma low_trunc_lemma_5 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (F : MvPowerSeries ι R) :
    ∀ e : ι →₀ ℕ, e.degree < m + 1 →
      MvPowerSeries.coeff e (F - (psTrunc m F : MvPowerSeries ι R)) = 0 := by
  intro e he
  first
  | (rw [map_sub, MvPolynomial.coeff_coe, psTrunc_eq, MvPowerSeries.coeff_truncTotal,
      sub_self] <;> exact he)
  | simp [psTrunc_eq, MvPowerSeries.coeff_truncTotal, he]

theorem psJet_mul {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f g : MvPowerSeries ι R) :
    psJet m (f * g) = psJet m f * psJet m g := by
  unfold psJet
  rw [← map_mul, Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_6
  intro e he
  have h1 := low_mul_lemma (G := g) (q := 0) (low_trunc_lemma_5 m f)
    (fun d hd => absurd hd (Nat.not_lt_zero _)) e (by omega)
  have h2 := low_mul_lemma (F := (psTrunc m f : MvPowerSeries ι R)) (p := 0)
    (fun d hd => absurd hd (Nat.not_lt_zero _)) (low_trunc_lemma_5 m g) e (by omega)
  have h3 := low_trunc_lemma_5 m (f * g) e he
  have hcoe : MvPolynomial.coeff e (psTrunc m (f * g) - psTrunc m f * psTrunc m g) =
      MvPowerSeries.coeff e ((f - (psTrunc m f : MvPowerSeries ι R)) * g +
        (psTrunc m f : MvPowerSeries ι R) * (g - (psTrunc m g : MvPowerSeries ι R)) -
        (f * g - (psTrunc m (f * g) : MvPowerSeries ι R))) := by
    rw [← MvPolynomial.coeff_coe, coe_sub_lemma_7, MvPolynomial.coe_mul]
    first
    | (congr 1; ring)
    | exact congrArg _ (by ring)
  rw [hcoe, map_sub, map_add, h1, h2, h3, add_zero, sub_zero]

theorem psJet_one {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) :
    psJet m (1 : MvPowerSeries ι R) = 1 := by
  unfold psJet
  first
  | rw [psTrunc_eq, ← MvPolynomial.coe_one, mk_trunc_coe, map_one]
  | (have h := mk_trunc_coe (R := R) (ι := ι) m 1
     rw [MvPolynomial.coe_one] at h
     rw [psTrunc_eq, h, map_one])

theorem psTrunc_mem_orig {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (g : MvPowerSeries τ R)
    (hg : MvPowerSeries.constantCoeff g = 0) : psTrunc m g ∈ orig R τ := by
  unfold psTrunc
  refine Ideal.sum_mem _ fun e _ => ?_
  by_cases he : e = 0
  · subst he
    first
    | simp [hg]
    | (rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, map_zero]; exact Ideal.zero_mem _)
  · obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext fun j => by simp [h j])
    have key : MvPolynomial.monomial e (MvPowerSeries.coeff e g) =
        MvPolynomial.monomial (e - Finsupp.single i 1) (MvPowerSeries.coeff e g) *
          MvPolynomial.X i := by
      have hs : e - Finsupp.single i 1 + Finsupp.single i 1 = e := by
        ext j
        by_cases h : j = i
        · subst h
          first
          | (simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same]; omega)
          | (simp [Finsupp.single_apply]; omega)
          | simp [Finsupp.single_apply]
        · first
          | (simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h)]; omega)
          | simp [Finsupp.single_apply, h, Ne.symm h]
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, hs]
    rw [key]
    refine Ideal.mul_mem_left _ _ ?_
    first
    | exact Ideal.subset_span ⟨i, rfl⟩
    | (unfold orig; exact Ideal.subset_span ⟨i, rfl⟩)

theorem aeval_coe_comp {σ τ : Type} (A : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i => (A i : MvPowerSeries τ R)) P =
      ((MvPolynomial.aeval A P : MvPolynomial τ R) : MvPowerSeries τ R) := by
  induction P using MvPolynomial.induction_on
  next c =>
    first
    | simp [MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
    | simp [MvPolynomial.algebraMap_eq]
    | (rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
        MvPolynomial.coe_C]; rfl)
    | (ext n; simp [MvPowerSeries.coeff_C, MvPolynomial.coeff_C, MvPolynomial.algebraMap_eq])
  next p q hp hq => simp only [map_add, MvPolynomial.coe_add, hp, hq]
  next p i hp => simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.coe_mul, hp]

private lemma low_pow_lemma_2 {τ : Type} {F : MvPowerSeries τ R}
    (hF : ∀ e : τ →₀ ℕ, e.degree < 1 → MvPowerSeries.coeff e F = 0) (n : ℕ) :
    ∀ e : τ →₀ ℕ, e.degree < n → MvPowerSeries.coeff e (F ^ n) = 0 := by
  induction n with
  | zero => exact fun e he => absurd he (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ]
    exact low_mul_lemma ih hF

private lemma low_prod_lemma_3 {τ σ : Type} (S : Finset σ) (F : σ → MvPowerSeries τ R) (k : σ → ℕ)
    (hF : ∀ s ∈ S, ∀ e : τ →₀ ℕ, e.degree < k s → MvPowerSeries.coeff e (F s) = 0) :
    ∀ e : τ →₀ ℕ, e.degree < ∑ s ∈ S, k s → MvPowerSeries.coeff e (∏ s ∈ S, F s) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro e he
    simp at he
  | @insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs]
    exact low_mul_lemma (hF s (Finset.mem_insert_self s S))
      (ih fun t ht => hF t (Finset.mem_insert_of_mem ht))

private lemma low_aeval_lemma_4 {σ τ : Type} (n : ℕ) (a b : σ → MvPowerSeries τ R)
    (hab : ∀ i, ∀ e : τ →₀ ℕ, e.degree < n → MvPowerSeries.coeff e (a i - b i) = 0)
    (P : MvPolynomial σ R) :
    ∀ e : τ →₀ ℕ, e.degree < n →
      MvPowerSeries.coeff e (MvPolynomial.aeval a P - MvPolynomial.aeval b P) = 0 := by
  induction P using MvPolynomial.induction_on
  next c =>
    intro e he
    simp
  next p q hp hq =>
    intro e he
    have h1 := hp e he
    have h2 := hq e he
    simp only [map_add, map_sub] at h1 h2 ⊢
    linear_combination h1 + h2
  next p i hp =>
    intro e he
    simp only [map_mul, MvPolynomial.aeval_X]
    have key : MvPolynomial.aeval a p * a i - MvPolynomial.aeval b p * b i =
        (MvPolynomial.aeval a p - MvPolynomial.aeval b p) * a i +
          MvPolynomial.aeval b p * (a i - b i) := by ring
    rw [key, map_add]
    have h1 := low_mul_lemma (G := a i) (q := 0) hp (fun d hd => absurd hd (Nat.not_lt_zero _)) e
      (by omega)
    have h2 := low_mul_lemma (F := MvPolynomial.aeval b p) (p := 0)
      (fun d hd => absurd hd (Nat.not_lt_zero _)) (hab i) e (by omega)
    rw [h1, h2, add_zero]

theorem psJet_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (m : ℕ)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : MvPowerSeries σ R) :
    psJet m (MvPowerSeries.subst a f) =
      jetMap (fun i => psTrunc m (a i)) (fun i => psTrunc_mem_orig m (a i) (ha i)) (psJet m f) := by
  have hS : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩
  have ha1 : ∀ i, ∀ e : τ →₀ ℕ, e.degree < 1 → MvPowerSeries.coeff e (a i) = 0 := by
    intro i e he
    have he0 : e = 0 := by
      first
      | exact (Finsupp.degree_eq_zero_iff e).1 (by omega)
      | exact Finsupp.degree_eq_zero_iff.1 (by omega)
    subst he0
    first
    | simpa using ha i
    | (rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact ha i)
  have hprod : ∀ d : σ →₀ ℕ, ∀ e : τ →₀ ℕ, e.degree < d.degree →
      MvPowerSeries.coeff e (d.prod fun s n => a s ^ n) = 0 := by
    intro d e he
    have hd : d.degree = ∑ s ∈ d.support, d s := by
      first
      | rfl
      | simp [Finsupp.degree]
    exact low_prod_lemma_3 d.support (fun s => a s ^ d s) (fun s => d s)
      (fun s _ => low_pow_lemma_2 (ha1 s) (d s)) e (lt_of_lt_of_eq he hd)
  have hr := low_trunc_lemma_5 m f
  have hsr : ∀ e : τ →₀ ℕ, e.degree < m + 1 →
      MvPowerSeries.coeff e (MvPowerSeries.subst a (f - (psTrunc m f : MvPowerSeries σ R))) = 0 := by
    intro e he
    rw [MvPowerSeries.coeff_subst hS]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    by_cases hd : d.degree < m + 1
    · rw [hr d hd, zero_smul]
    · first
      | rw [hprod d e (by omega), smul_zero]
      | simp [hprod d e (by omega)]
  have hsplit : MvPowerSeries.subst a f = MvPolynomial.aeval a (psTrunc m f) +
      MvPowerSeries.subst a (f - (psTrunc m f : MvPowerSeries σ R)) := by
    first
    | (rw [← MvPowerSeries.subst_coe, ← MvPowerSeries.subst_add hS]
       congr 1
       ring)
    | (have h := MvPowerSeries.subst_add hS (psTrunc m f : MvPowerSeries σ R)
         (f - (psTrunc m f : MvPowerSeries σ R))
       rw [MvPowerSeries.subst_coe] at h
       rw [← h]
       congr 1
       ring)
  unfold psJet
  rw [jetMap_mk, Ideal.Quotient.eq]
  apply mem_orig_pow_lemma_6
  intro e he
  have hA := low_aeval_lemma_4 (m + 1) a (fun i => (psTrunc m (a i) : MvPowerSeries τ R))
    (fun i => low_trunc_lemma_5 m (a i)) (psTrunc m f) e he
  have hT := low_trunc_lemma_5 m (MvPowerSeries.subst a f) e he
  have hcoe : MvPolynomial.coeff e (psTrunc m (MvPowerSeries.subst a f) -
        MvPolynomial.aeval (fun i => psTrunc m (a i)) (psTrunc m f)) =
      MvPowerSeries.coeff e ((MvPolynomial.aeval a (psTrunc m f) -
          MvPolynomial.aeval (fun i => (psTrunc m (a i) : MvPowerSeries τ R)) (psTrunc m f)) +
        MvPowerSeries.subst a (f - (psTrunc m f : MvPowerSeries σ R)) -
        (MvPowerSeries.subst a f - (psTrunc m (MvPowerSeries.subst a f) : MvPowerSeries τ R))) := by
    rw [← MvPolynomial.coeff_coe, coe_sub_lemma_7, ← aeval_coe_comp]
    first
    | (congr 1; linear_combination hsplit)
    | exact congrArg _ (by linear_combination hsplit)
  rw [hcoe, map_sub, map_add, hA, hsr e he, hT, add_zero, sub_zero]

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
