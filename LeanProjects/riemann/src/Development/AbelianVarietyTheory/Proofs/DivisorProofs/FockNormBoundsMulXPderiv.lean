import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockNormBound

theorem norm_sum_sq_of_orth {κ H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : Finset κ) (v : κ → H) (h : ∀ a b, a ≠ b → inner ℂ (v a) (v b) = 0) :
    ‖∑ a ∈ s, v a‖ ^ 2 = ∑ a ∈ s, ‖v a‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [inner_sum, Finset.sum_eq_single a, inner_self_eq_norm_sq]
  · intro b _ hb; exact h a b (Ne.symm hb)
  · intro h'; exact absurd ha h'

def mfact {σ : Type} (α : σ →₀ ℕ) : ℝ := α.prod (fun _ k => (k.factorial : ℝ))

theorem mfact_nonneg {σ : Type} (α : σ →₀ ℕ) : 0 ≤ mfact α :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem mfact_add {σ : Type} [DecidableEq σ] (α : σ →₀ ℕ) (i : σ) :
    mfact (α + Finsupp.single i 1) = ((α i : ℝ) + 1) * mfact α := by
  unfold mfact
  rw [← Finsupp.mul_prod_erase' (α + Finsupp.single i 1) i _ (by simp),
    ← Finsupp.mul_prod_erase' α i _ (by simp)]
  have : Finsupp.erase i (α + Finsupp.single i 1) = Finsupp.erase i α := by
    ext j; by_cases hj : j = i
    · simp [hj]
    · simp [Finsupp.erase_ne hj, Finsupp.single_eq_of_ne hj]
  rw [this]
  simp [Nat.factorial_succ]
  ring

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem norm_mono (h : IsFockIP ι) (α : σ →₀ ℕ) : ‖ι (monomial α 1)‖ ^ 2 = mfact α := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h α α, if_pos rfl]
  have : α.prod (fun _ k => (k.factorial : ℂ)) = ((mfact α : ℝ) : ℂ) := by
    simp [mfact, Finsupp.prod]
  rw [this]; simp

theorem norm_comb (h : IsFockIP ι) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℂ)
    (g : (σ →₀ ℕ) → (σ →₀ ℕ)) (hg : ∀ a b, a ≠ b → c a ≠ 0 → c b ≠ 0 → g a ≠ g b) :
    ‖ι (∑ a ∈ s, monomial (g a) (c a))‖ ^ 2 = ∑ a ∈ s, ‖c a‖ ^ 2 * mfact (g a) := by
  have e : ∀ a, ι (monomial (g a) (c a)) = c a • ι (monomial (g a) 1) := by
    intro a; rw [← map_smul, smul_monomial]; simp
  rw [map_sum, norm_sum_sq_of_orth]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [e, norm_smul, mul_pow, norm_mono h]
  · intro a b hab
    rw [e, e]
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    rw [inner_smul_left, inner_smul_right, h, if_neg (hg a b hab ha hb)]; simp

theorem fock_norm_bounds (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (h : IsFockIP ι) (i : σ) (d : ℕ)
    (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧
      ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  have hd : ∀ a ∈ P.support, (a i : ℝ) ≤ d := by
    intro a ha
    have h1 : a i ≤ P.degreeOf i := monomial_le_degreeOf i ha
    exact_mod_cast h1.trans ((degreeOf_le_totalDegree P i).trans hP)
  have h0 : ‖ι P‖ ^ 2 = ∑ a ∈ P.support, ‖coeff a P‖ ^ 2 * mfact a := by
    conv_lhs => rw [P.as_sum]
    exact norm_comb h _ _ id (fun a b hab _ _ => hab)
  have h1 : X i * P = ∑ a ∈ P.support, monomial (a + Finsupp.single i 1) (coeff a P) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [X, monomial_mul, add_comm, one_mul]
  have h2 : pderiv i P = ∑ a ∈ P.support, monomial (a - Finsupp.single i 1) (coeff a P * a i) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pderiv_monomial]
  have hsub : ∀ a : σ →₀ ℕ, a i ≠ 0 → a - Finsupp.single i 1 + Finsupp.single i 1 = a := by
    intro a ha
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ha))
  constructor
  · rw [h1, norm_comb h _ _ _ (fun a b hab _ _ hh => hab (add_right_cancel hh)), h0,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [mfact_add]
    have := hd a ha
    have h3 : 0 ≤ ‖coeff a P‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
    nlinarith
  · rw [h2, norm_comb h, h0, Finset.mul_sum]
    · refine Finset.sum_le_sum fun a ha => ?_
      have h3 : 0 ≤ ‖coeff a P‖ ^ 2 * mfact a := mul_nonneg (by positivity) (mfact_nonneg a)
      by_cases hz : a i = 0
      · simp only [hz, Nat.cast_zero, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, zero_mul]
        exact mul_nonneg (by positivity) h3
      have h4 := mfact_add (a - Finsupp.single i 1) i
      rw [hsub a hz] at h4
      have h5 : (((a - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : ℝ) + 1 = a i := by
        have := congrArg (fun f : σ →₀ ℕ => f i) (hsub a hz)
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
        exact_mod_cast this
      rw [h5] at h4
      rw [norm_mul, Complex.norm_natCast]
      calc (‖coeff a P‖ * a i) ^ 2 * mfact (a - Finsupp.single i 1)
          = a i * (‖coeff a P‖ ^ 2 * mfact a) := by rw [h4]; ring
        _ ≤ d * (‖coeff a P‖ ^ 2 * mfact a) := mul_le_mul_of_nonneg_right (hd a ha) h3
    · intro a b hab ha hb hh
      have ha' : a i ≠ 0 := fun z => ha (by simp [z])
      have hb' : b i ≠ 0 := fun z => hb (by simp [z])
      apply hab
      rw [← hsub a ha', hh, hsub b hb']

end GlobalTheory.FockNormBound
