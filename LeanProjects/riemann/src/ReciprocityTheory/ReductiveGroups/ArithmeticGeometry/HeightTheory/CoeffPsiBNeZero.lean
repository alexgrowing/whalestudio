import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

namespace ReciprocityTheory.ChartRestriction.G.T0.MHF

open MvPolynomial ReciprocityTheory.MultiplicativeHeights

variable {K : Type*} [Field K] {B n : ℕ}

def bw (b : Fin B) (s : Fin B × Fin n →₀ ℕ) : ℕ := ∑ j, s (b, j)

theorem bw_add (b : Fin B) (s t : Fin B × Fin n →₀ ℕ) : bw b (s + t) = bw b s + bw b t := by
  simp [bw, Finset.sum_add_distrib]

theorem bw_single (b : Fin B) (v : Fin B × Fin n) (e : ℕ) :
    bw b (Finsupp.single v e) = if v.1 = b then e else 0 := by
  obtain ⟨i, j⟩ := v
  by_cases h : i = b
  · subst h; simp [bw, Finsupp.single_apply]
  · simp [bw, Finsupp.single_apply, h]

noncomputable def psiB (b : Fin B) :
    MvPolynomial (Fin B × Fin n) K →ₐ[K] Polynomial (MvPolynomial (Fin B × Fin n) K) :=
  aeval fun v => if v.1 = b then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiB_X (b : Fin B) (v : Fin B × Fin n) :
    psiB (K := K) b (X v) = Polynomial.C (X v) * Polynomial.X ^ (if v.1 = b then 1 else 0) := by
  simp only [psiB, aeval_X]; split_ifs <;> simp

theorem psiB_monomial (b : Fin B) (s : Fin B × Fin n →₀ ℕ) (a : K) :
    psiB b (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ bw b s := by
  induction s using Finsupp.induction generalizing a
  · simp [psiB, bw, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  · rename_i v e f _ _ ih
    rw [monomial_single_add, map_mul, map_pow, ih, psiB_X, bw_add, bw_single]
    split_ifs <;> simp only [map_mul, map_pow, mul_pow, ← pow_mul, pow_add, mul_one, mul_zero,
      pow_zero, add_zero, zero_add] <;> ring

theorem psiB_eq_of_hom (b : Fin B) (δ : ℕ) (f : MvPolynomial (Fin B × Fin n) K)
    (hf : ∀ s ∈ f.support, bw b s = δ) : psiB b f = Polynomial.C f * Polynomial.X ^ δ := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s hs => by rw [psiB_monomial, hf s hs]

theorem coeff_psiB_ne_zero (b : Fin B) (f : MvPolynomial (Fin B × Fin n) K)
    (s : Fin B × Fin n →₀ ℕ) (hs : s ∈ f.support) : (psiB b f).coeff (bw b s) ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (MvPolynomial.coeff s) h0
  conv at h1 => lhs; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, coeff_sum] at h1
  simp only [psiB_monomial, Polynomial.coeff_C_mul_X_pow, coeff_zero] at h1
  rw [Finset.sum_eq_single s] at h1
  · simp at h1; exact (mem_support_iff.1 hs) h1
  · intro s' _ hne
    split_ifs <;> simp [coeff_monomial, hne]
  · intro h; exact absurd hs h

theorem ntd_pow {R : Type*} [CommRing R] [IsDomain R] (p : Polynomial R) (hp : p ≠ 0) (m : ℕ) :
    (p ^ m).natTrailingDegree = m * p.natTrailingDegree := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.natTrailingDegree_mul (pow_ne_zero _ hp) hp, ih, Nat.succ_mul]

theorem isMH_of_pow (hB : 0 < B) (F0 : MvPolynomial (Fin B × Fin n) K) (κ : K) (m δ : ℕ)
    (hm : 1 ≤ m) (hκ : κ ≠ 0) (hF0 : F0 ≠ 0)
    (h : IsMultiHomogeneous (fun _ => δ) (C κ * F0 ^ m)) :
    ∃ d0, m * d0 = δ ∧ IsMultiHomogeneous (fun _ => d0) F0 := by
  classical
  have key : ∀ b : Fin B, ∃ k, m * k = δ ∧ ∀ s ∈ F0.support, bw b s = k := by
    intro b
    have h1 := psiB_eq_of_hom b δ _ (fun s hs => h s hs b)
    rw [map_mul, map_pow, show psiB b (C κ) = Polynomial.C (C κ) by
      simp [psiB, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply], map_mul] at h1
    have hCk : (Polynomial.C (C κ) : Polynomial (MvPolynomial (Fin B × Fin n) K)) ≠ 0 := by
      simp [hκ]
    have h2 : psiB b F0 ^ m = Polynomial.C (F0 ^ m) * Polynomial.X ^ δ := by
      apply mul_left_cancel₀ hCk
      rw [h1, map_pow]; ring
    obtain ⟨s0, hs0⟩ : F0.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.2 fun h0 => hF0 (support_eq_empty.1 h0)
    have hP : psiB b F0 ≠ 0 := fun h0 => coeff_psiB_ne_zero b F0 s0 hs0 (by rw [h0]; simp)
    have hFm : F0 ^ m ≠ 0 := pow_ne_zero _ hF0
    have hdeg := congrArg Polynomial.natDegree h2
    have htr := congrArg Polynomial.natTrailingDegree h2
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_C_mul_X_pow _ _ hFm] at hdeg
    rw [ntd_pow _ hP, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hFm] at htr
    have heq : (psiB b F0).natDegree = (psiB b F0).natTrailingDegree :=
      Nat.eq_of_mul_eq_mul_left hm (hdeg.trans htr.symm)
    refine ⟨(psiB b F0).natDegree, hdeg, fun s hs => ?_⟩
    have hc := coeff_psiB_ne_zero b F0 s hs
    have h3 := Polynomial.le_natDegree_of_ne_zero hc
    have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
    omega
  obtain ⟨k0, hk0, -⟩ := key ⟨0, hB⟩
  refine ⟨k0, hk0, fun s hs b => ?_⟩
  obtain ⟨k, hk, hks⟩ := key b
  rw [show (∑ j, s (b, j)) = bw b s from rfl, hks s hs]
  exact Nat.eq_of_mul_eq_mul_left hm (hk.trans hk0.symm)

end ReciprocityTheory.ChartRestriction.G.T0.MHF
