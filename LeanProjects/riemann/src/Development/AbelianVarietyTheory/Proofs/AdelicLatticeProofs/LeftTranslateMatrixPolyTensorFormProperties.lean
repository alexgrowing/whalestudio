import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_monomial_eq_prod_X {σ : Type} (n : ℕ) : ∀ d : σ →₀ ℕ, d.degree = n →
    ∃ a : Fin n → σ, (MvPolynomial.monomial d (1 : ℂ)) = ∏ k, MvPolynomial.X (a k) := by
  classical
  induction n with
  | zero =>
    intro d hd
    rw [Finsupp.degree_eq_zero_iff] at hd
    subst hd
    exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro d hd
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    have hle : Finsupp.single i 1 ≤ d := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr hi
    obtain ⟨d', rfl⟩ := exists_add_of_le hle
    have hd' : d'.degree = n := by
      rw [map_add, Finsupp.degree_single] at hd
      omega
    obtain ⟨a, ha⟩ := ih d' hd'
    refine ⟨Fin.cons i a, ?_⟩
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← ha, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC, map_add] at *
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul] at *
    rw [hp]
    simp [ltr, Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem evC_ext {f f' : MvPolynomial (ι × ι) ℂ} (h : ∀ y, evC f y = evC f' y) : f = f' := by
  apply MvPolynomial.funext
  intro x
  exact h (Matrix.of fun i j => x (i, j))

theorem tpow_mul_complex (n : ℕ) (y z : Matrix ι ι ℂ) : tpow n (y * z) = tpow n y * tpow n z := by
  ext a b
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

noncomputable def tensorForm (n : ℕ) (b : Fin n → ι) : ((Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ :=
  ∑ a : Fin n → ι, (LinearMap.proj a).smulRight (∏ k, MvPolynomial.X (a k, b k))

theorem tensorForm_apply (n : ℕ) (b : Fin n → ι) (l : (Fin n → ι) → ℂ) :
    tensorForm n b l = ∑ a : Fin n → ι, l a • ∏ k, MvPolynomial.X (a k, b k) := by
  simp [tensorForm, LinearMap.sum_apply]

theorem evC_tensorForm (n : ℕ) (b : Fin n → ι) (l : (Fin n → ι) → ℂ) (y : Matrix ι ι ℂ) :
    evC (tensorForm n b l) y = (l ᵥ* tpow n y) b := by
  rw [tensorForm_apply]
  simp [evC, tpow, Matrix.vecMul, dotProduct, map_sum, map_prod]

theorem ltr_tensorForms : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ), evC (ltr g f) y = evC f (g * y)) ∧ (∀ (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ), IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f) ∧ (∀ (g : Matrix ι ι ℂ) (n : ℕ) (f : MvPolynomial (ι × ι) ℂ), f.IsHomogeneous n → (ltr g f).IsHomogeneous n) ∧ ∀ n : ℕ, ∃ p : (Fin n → ι) → ((Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ, (∀ b l (y : Matrix ι ι ℂ), evC (p b l) y = (l ᵥ* tpow n y) b) ∧ (∀ b l (g : Matrix ι ι ℂ), ltr g (p b l) = p b (l ᵥ* tpow n g)) ∧ ∀ f : MvPolynomial (ι × ι) ℂ, f.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, f = ∑ b, p b (l b) := by
  intro ι _ _
  refine ⟨evC_ltr, ?_, ?_, ?_⟩
  · intro Γ f
    constructor
    · intro h g hg
      exact evC_ext fun y => by rw [evC_ltr, h g hg]
    · intro h g hg y
      rw [← evC_ltr, h g hg]
  · intro g n f hf
    have := hf.aeval (S := ℂ) (n := 1)
      (fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * MvPolynomial.X (k, ij.2)) (fun ij =>
        MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
    rw [one_mul] at this
    exact this
  · intro n
    refine ⟨tensorForm n, evC_tensorForm n, ?_, ?_⟩
    · intro b l g
      apply evC_ext
      intro y
      rw [evC_ltr, evC_tensorForm, evC_tensorForm, tpow_mul_complex, Matrix.vecMul_vecMul]
    · intro f hf
      let Φ : ((Fin n → ι) → (Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ :=
        ∑ b, (tensorForm n b).comp (LinearMap.proj b)
      have hΦ : ∀ l, Φ l = ∑ b, tensorForm n b (l b) := by
        intro l
        simp [Φ, LinearMap.sum_apply]
      suffices h : f ∈ LinearMap.range Φ by
        obtain ⟨l, hl⟩ := h
        exact ⟨l, by rw [← hΦ, hl]⟩
      rw [f.as_sum]
      refine Submodule.sum_mem _ fun d hd => ?_
      have hdeg : d.degree = n := by
        by_contra h
        exact (MvPolynomial.mem_support_iff.mp hd) (hf.coeff_eq_zero h)
      obtain ⟨a, ha⟩ := exists_monomial_eq_prod_X n d hdeg
      have h1 : MvPolynomial.monomial d (f.coeff d) = f.coeff d • MvPolynomial.monomial d (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [h1, ha]
      refine Submodule.smul_mem _ _ ⟨Pi.single (fun k => (a k).2) (Pi.single (fun k => (a k).1) 1), ?_⟩
      rw [hΦ, Finset.sum_eq_single (fun k => (a k).2)]
      · rw [Pi.single_eq_same, tensorForm_apply, Finset.sum_eq_single (fun k => (a k).1)]
        · simp
        · intro c _ hc
          simp [hc]
        · simp
      · intro c _ hc
        simp [hc]
      · simp

end GlobalTheory.ClassFin
