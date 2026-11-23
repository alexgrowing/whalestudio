import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.LocInstH

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (coeff m p).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ m ∈ p.support, monomial m (coeff m p).im

theorem coeff_reP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : coeff m (reP p) = (coeff m p).re := by
  classical
  unfold reP
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : coeff m p = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem coeff_imP (p : MvPolynomial σ ℂ) (m : σ →₀ ℕ) : coeff m (imaginary p) = (coeff m p).im := by
  classical
  unfold imaginary
  rw [coeff_sum]
  by_cases h : m ∈ p.support
  · rw [Finset.sum_eq_single m (fun b _ hb => by rw [coeff_monomial, if_neg hb]) (fun hm => absurd h hm), coeff_monomial, if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => by rw [coeff_monomial, if_neg (fun (e : b = m) => h (e ▸ hb))])]
    have h0 : coeff m p = 0 := by simpa [mem_support_iff] using h
    simp [h0]

theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = map (algebraMap ℝ ℂ) (reP p) + C Complex.I * map (algebraMap ℝ ℂ) (imaginary p) := by
  ext m
  rw [coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_reP, coeff_imP]
  apply Complex.ext <;> simp

theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, eval (fun i => (y i : ℂ)) p = 0) : p = 0 := by
  have hev : ∀ (y : σ → ℝ) (q : MvPolynomial σ ℝ),
      eval (fun i => (y i : ℂ)) (map (algebraMap ℝ ℂ) q) = ((eval y q : ℝ) : ℂ) := by
    intro y q
    rw [eval_map]
    change _ = (algebraMap ℝ ℂ) (eval₂ (RingHom.id ℝ) y q)
    rw [hom_eval₂]
    rfl
  have key : ∀ y : σ → ℝ, eval y (reP p) = 0 ∧ eval y (imaginary p) = 0 := by
    intro y
    have hy := h y
    rw [eq_map_re_add_im p, eval_add, eval_mul, eval_C, hev, hev] at hy
    have hre := congrArg Complex.re hy
    have him := congrArg Complex.im hy
    simp at hre him
    exact ⟨hre, him⟩
  have hr : reP p = 0 := MvPolynomial.funext fun y => by simpa using (key y).1
  have hi : imaginary p = 0 := MvPolynomial.funext fun y => by simpa using (key y).2
  rw [eq_map_re_add_im p, hr, hi]
  simp

end PositivityTheory.Rg.Sw.Glob.LocInstH
