import Mathlib
import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.SolveV

set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.FG.SolveVAux

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {σ τ : Type}

theorem low_pderiv {N : ℕ} {g : MvPowerSeries τ k} (hg : Low (N + 1) g) (t : τ) : Low N (pderiv k t g) := by
  intro d hd
  rw [MvPowerSeries.coeff_pderiv, hg, zero_mul]
  have e : Finsupp.degree (d + Finsupp.single t 1) = Finsupp.degree d + 1 := by
    first
    | rw [map_add, Finsupp.degree_single]
    | simp [Finsupp.degree, Finsupp.sum_add_index']
    | (unfold Finsupp.degree; rw [Finsupp.sum_add_index' (by simp) (by simp)]; simp)
  omega

private theorem low_mul_lemma {m n : ℕ} {f g : MvPowerSeries τ k} (hf : Low m f) (hg : Low n g) :
    Low (m + n) (f * g) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  | simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  | simp only [Finset.mem_antidiagonal] at hx
  have e : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree d := by
    rw [← hx]
    first
    | exact (map_add _ _ _).symm
    | simp [Finsupp.degree, Finsupp.sum_add_index']
  by_cases h1 : Finsupp.degree x.1 < m
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

private theorem low_pow_lemma_2 {f : MvPowerSeries τ k} (hf : Low 1 f) (n : ℕ) : Low n (f ^ n) := by
  induction n with
  | zero => intro d hd; omega
  | succ n ih => rw [pow_succ]; exact low_mul_lemma ih hf

private theorem low_prod_lemma_3 {a : σ → MvPowerSeries τ k} (ha : ∀ s, Low 1 (a s)) (e : σ →₀ ℕ)
    (S : Finset σ) : Low (∑ s ∈ S, e s) (∏ s ∈ S, a s ^ e s) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · intro d hd
    simp at hd
  · intro s S hs ih
    rw [Finset.sum_insert hs, Finset.prod_insert hs]
    exact low_mul_lemma (low_pow_lemma_2 (ha s) _) ih

private theorem finsupp_apply_le_degree' {ι : Type} (d : ι →₀ ℕ) (i : ι) : d i ≤ d.degree := by
  first
  | exact Finsupp.le_degree i d
  | exact Finsupp.le_degree d i
  | exact Finsupp.le_degree

theorem low_subst_of_low [Finite σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, Low 1 (a s)) {N : ℕ}
    {g : MvPowerSeries σ k} (hg : Low N g) : Low N (subst a g) := by
  classical
  have hc : ∀ s, constantCoeff (a s) = 0 := fun s => by
    have h0 := ha s 0 (by simp)
    simpa using h0
  intro d hd
  have hS : HasSubst a := by
    exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  rw [MvPowerSeries.coeff_subst hS]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e.degree < N
  · exact smul_eq_zero_of_left (hg e he) _
  · have hl : Low e.degree (e.prod fun s n => a s ^ n) := by
      have h := low_prod_lemma_3 ha e e.support
      have hdeg : e.degree = ∑ s ∈ e.support, e s := by
        first
        | rfl
        | exact Finsupp.degree_eq_sum e
        | simp [Finsupp.degree]
      rw [hdeg]
      exact h
    exact smul_eq_zero_of_right _ (hl d (by omega))

theorem pderiv_aeval [Fintype σ] (a : σ → MvPowerSeries τ k) (p : MvPolynomial σ k) (t : τ) :
    pderiv k t (MvPolynomial.aeval a p) =
      ∑ s, MvPolynomial.aeval a (MvPolynomial.pderiv s p) * pderiv k t (a s) := by
  classical
  induction p using MvPolynomial.induction_on
  next c =>
    simp
  next p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  next p s0 hp =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, map_add, map_mul,
      MvPolynomial.aeval_X, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, map_one, map_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [apply_ite (MvPolynomial.aeval a), map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, mul_assoc]
    try ring

private theorem pderiv_coe_mvPolynomial (s : σ) (p : MvPolynomial σ k) :
    pderiv k s (p : MvPowerSeries σ k) = ((MvPolynomial.pderiv s p : MvPolynomial σ k) : MvPowerSeries σ k) := by
  ext m
  rw [MvPowerSeries.coeff_pderiv, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, MvPolynomial.coeff_pderiv]

private theorem Low_finset_sum {N : ℕ} {ι : Type} (S : Finset ι) (F : ι → MvPowerSeries τ k)
    (h : ∀ i ∈ S, Low N (F i)) : Low N (∑ i ∈ S, F i) := by
  intro d hd
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi d hd

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ k) (t : τ) :
    pderiv k t (subst a f) = ∑ s, subst a (pderiv k s f) * pderiv k t (a s) := by
  classical
  have hS : HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have ha1 : ∀ s, Low 1 (a s) := by
    intro s d hd
    have hd0 : d = 0 := Finsupp.ext fun i => by
      have := finsupp_apply_le_degree' d i
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    subst hd0
    simpa using ha s
  have hpoly : ∀ M : ℕ, ∃ p : MvPolynomial σ k, Low M (f - (p : MvPowerSeries σ k)) := by
    intro M
    refine ⟨MvPowerSeries.trunc' k (Finsupp.equivFunOnFinite.symm fun _ => M) f, ?_⟩
    intro m hm
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos, sub_self]
    rw [Finsupp.le_def]
    intro s
    have h1 := finsupp_apply_le_degree' m s
    first
    | (change m s ≤ M; omega)
    | (simp; omega)
  ext d
  obtain ⟨p, hp⟩ := hpoly (d.degree + 1 + 1)
  have hf : f = (f - (p : MvPowerSeries σ k)) + (p : MvPowerSeries σ k) := (sub_add_cancel _ _).symm
  generalize f - (p : MvPowerSeries σ k) = g at hp hf
  subst hf
  have hpol := pderiv_aeval a p t
  simp only [map_add, MvPowerSeries.subst_add hS, MvPowerSeries.subst_coe, pderiv_coe_mvPolynomial, add_mul,
    Finset.sum_add_distrib, hpol]
  congr 1
  have h1 : Low (d.degree + 1) (pderiv k t (subst a g)) := low_pderiv (low_subst_of_low ha1 hp) t
  have h2 : Low (d.degree + 1 + 0) (∑ s, subst a (pderiv k s g) * pderiv k t (a s)) :=
    Low_finset_sum _ _ fun s _ => low_mul_lemma (low_subst_of_low ha1 (low_pderiv hp s)) (fun e he => by omega)
  rw [h1 d (by omega), h2 d (by omega)]

theorem pderiv_comm (u v : τ) (g : MvPowerSeries τ k) : pderiv k u (pderiv k v g) = pderiv k v (pderiv k u g) := by
  ext n
  simp only [MvPowerSeries.coeff_pderiv]
  by_cases huv : u = v
  · subst huv
    rfl
  · have h1 : (n + Finsupp.single u 1 : τ →₀ ℕ) v = n v := by simp [Finsupp.single_apply, huv]
    have h2 : (n + Finsupp.single v 1 : τ →₀ ℕ) u = n u := by simp [Finsupp.single_apply, Ne.symm huv]
    rw [h1, h2, add_right_comm n]
    ring

theorem eq_C_of_pderiv_zero [Algebra ℚ k] {g : MvPowerSeries τ k} (h : ∀ v, pderiv k v g = 0) :
    g = C (constantCoeff g) := by
  classical
  ext n
  rw [MvPowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    simp
  · obtain ⟨v, hv⟩ : ∃ v, n v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hn (Finsupp.ext fun i => by simpa using hcon i)
    set m := n - Finsupp.single v 1 with hm
    have hnm : n = m + Finsupp.single v 1 :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv))).symm
    have h0 := congrArg (MvPowerSeries.coeff m) (h v)
    rw [MvPowerSeries.coeff_pderiv, ← hnm, map_zero] at h0
    have hu : IsUnit ((m v : k) + 1) := by
      have e : ((m v : k) + 1) = algebraMap ℚ k ((m v : ℚ) + 1) := by simp
      rw [e]
      exact (IsUnit.mk0 _ (by positivity)).map _
    exact (hu.mul_left_eq_zero).mp h0

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
