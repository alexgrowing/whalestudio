import Formalism.PeriodIntegrals.HookBound
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookLower

def diagHom (N : ℕ) : MvPolynomial (Fin N × Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N × Fin N) ℚ :=
  aeval fun v => if v.1 = v.2 then X v else 0

def IsDiag {N : ℕ} (m : Fin N × Fin N →₀ ℕ) : Prop := ∀ v : Fin N × Fin N, v.1 ≠ v.2 → m v = 0

open scoped Classical in
theorem diagHom_monomial {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (c : ℚ) :
    diagHom N (monomial m c) = if IsDiag m then monomial m c else 0 := by
  classical
  rw [diagHom, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    have : v.1 = v.2 := by
      by_contra hne
      exact (Finsupp.mem_support_iff.1 hv) (h v hne)
    rw [if_pos this]
  · have : ∃ v, v.1 ≠ v.2 ∧ m v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h fun v hv => by_contra fun h0 => h0 (hc v hv)
    obtain ⟨v, hv, hmv⟩ := this
    rw [Finsupp.prod, Finset.prod_eq_zero (i := v) (Finsupp.mem_support_iff.2 hmv), mul_zero]
    rw [if_neg hv, zero_pow hmv]

theorem coeff_diagHom {N : ℕ} (f : MvPolynomial (Fin N × Fin N) ℚ) (m : Fin N × Fin N →₀ ℕ)
    (hm : IsDiag m) : coeff m (diagHom N f) = coeff m f := by
  classical
  refine MvPolynomial.induction_on' f (fun μ c => ?_) (fun p q hp hq => ?_)
  · rw [diagHom_monomial]
    split_ifs with h
    · rfl
    · rw [coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact h hm
  · rw [map_add, coeff_add, coeff_add, hp, hq]

def diagMono {N : ℕ} (s : ℕ) (h : s ≤ N) : Fin N × Fin N →₀ ℕ :=
  ∑ p : Fin s, Finsupp.single (Fin.castLE h p, Fin.castLE h p) 1

theorem diagHom_lpMinor {N : ℕ} (s : ℕ) (hr hn : s ≤ N) :
    diagHom N (lpMinor ℚ s hr hn) = monomial (diagMono s hr) 1 := by
  classical
  rw [lpMinor, AlgHom.map_det]
  have hM : (diagHom N).mapMatrix
      (Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin N × Fin N) ℚ)) =
      Matrix.diagonal fun p : Fin s => (X (Fin.castLE hr p, Fin.castLE hr p) : MvPolynomial (Fin N × Fin N) ℚ) := by
    ext p q
    by_cases hpq : p = q
    · subst hpq
      simp [diagHom]
    · have : ¬ (Fin.castLE hr p = Fin.castLE hn q) := by
        intro h
        apply hpq
        exact Fin.ext (by simpa [Fin.ext_iff] using h)
      simp [diagHom, hpq, this]
  rw [hM, Matrix.det_diagonal, diagMono, monomial_sum_one]
  rfl

def M0 {N : ℕ} (ν : Fin N → ℕ) : Fin N × Fin N →₀ ℕ :=
  ∑ s : Fin N, (ν s - nuNext ν s) • diagMono (s.val + 1) s.isLt

theorem diagHom_hw {N : ℕ} (ν : Fin N → ℕ) :
    diagHom N (hw ℚ le_rfl ν) = monomial (M0 ν) 1 := by
  classical
  rw [hw, map_prod, M0, monomial_sum_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, diagHom_lpMinor, monomial_pow, one_pow]

theorem isDiag_diagonal_monomial {N : ℕ} (ν : Fin N → ℕ) : IsDiag (M0 ν) := by
  classical
  intro v hv
  simp only [M0, diagMono, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro p _
  rw [Finsupp.single_apply, if_neg]
  intro h
  subst h
  exact hv rfl

theorem coeff_diagonal_monomial_hw {N : ℕ} (ν : Fin N → ℕ) : coeff (M0 ν) (hw ℚ le_rfl ν) = 1 := by
  rw [← coeff_diagHom _ _ (isDiag_diagonal_monomial ν), diagHom_hw, coeff_monomial, if_pos rfl]

theorem weight_rowW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    (Finsupp.weight (rowW N N) m) a = ∑ b : Fin N, m (a, b) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  simp only [Pi.smul_apply, rowW, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem diagonal_monomial_apply {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) (a : Fin N) : M0 ν (a, a) = ν a := by
  classical
  have hmem : coeff (M0 ν) (hw ℚ le_rfl ν) ≠ 0 := by rw [coeff_diagonal_monomial_hw]; exact one_ne_zero
  have hw8 := hwRowWeight ℚ N N le_rfl ν hν hmem
  have h1 := congrFun hw8 a
  rw [weight_rowW_apply, Finset.sum_eq_single a] at h1
  · rw [h1]
    simp [rowNu]
  · intro b _ hb
    exact isDiag_diagonal_monomial ν (a, b) (Ne.symm hb)
  · simp

theorem diagonal_monomial_factorial {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) :
    (∏ k ∈ (M0 ν).support, ((M0 ν) k).factorial) = ∏ l, (ν l).factorial := by
  classical
  rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.1 hk]; rfl)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_eq_single a]
  · rw [diagonal_monomial_apply ν hν a]
  · intro b _ hb
    rw [isDiag_diagonal_monomial ν (a, b) (Ne.symm hb)]
    rfl
  · simp

theorem fockQ_hw_ge {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) :
    (∏ l, ((ν l).factorial : ℚ)) ≤ fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  classical
  have hmem : M0 ν ∈ (hw ℚ le_rfl ν).support := by
    rw [mem_support_iff, coeff_diagonal_monomial_hw]; exact one_ne_zero
  unfold fockQ
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun m =>
      coeff m (hw ℚ le_rfl ν) * coeff m (hw ℚ le_rfl ν) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ))
    (fun m _ => mul_nonneg (mul_self_nonneg _) (Nat.cast_nonneg _)) hmem)
  simp only [coeff_diagonal_monomial_hw, one_mul]
  rw [diagonal_monomial_factorial ν hν]
  push_cast
  rfl

theorem one_le_cNu {N : ℕ} (ν : Fin N → ℕ) (hν : Antitone ν) : 1 ≤ PI.cNu ν := by
  have h := fockQ_hw_ge ν hν
  have hpos : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
  have h' : (∏ l, ((ν l).factorial : ℝ)) ≤ ((fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℚ) : ℝ) := by
    exact_mod_cast h
  unfold PI.cNu
  rw [one_le_div hpos]
  exact h'

end PI.HookLower
