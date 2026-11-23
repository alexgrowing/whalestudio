import Mathlib

noncomputable def UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm :
    {g : ℕ} → Matrix (Fin g) (Fin g) ℂ → (Fin g → ℂ) → (Fin g → ℂ) → ℂ :=
    fun {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) ↦ z ⬝ᵥ Hm.mulVec (Star.star w)

noncomputable def UpperTheory.Reformulated.B.HermitianFormImEqSum.hv :
    {n : ℕ} → Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) ↦ Star.star y ⬝ᵥ M.mulVec x

private theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span {V : Type} [AddCommGroup V] [Module ℝ V]
    (f h : V → ℝ) (S : Set V) (hS : Submodule.span ℝ S = ⊤)
    (fa : ∀ x y, f (x + y) = f x + f y) (fs : ∀ (c : ℝ) x, f (c • x) = c * f x)
    (ha : ∀ x y, h (x + y) = h x + h y) (hs : ∀ (c : ℝ) x, h (c • x) = c * h x)
    (H : ∀ a ∈ S, f a = h a) (x : V) : f x = h x := by
  have hx : x ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem a ha => exact H a ha
  | zero =>
    have h1 := fs 0 0
    have h2 := hs 0 0
    simp only [zero_smul, zero_mul] at h1 h2
    rw [h1, h2]
  | add a b _ _ h1 h2 => rw [fa, ha, h1, h2]
  | smul c a _ h1 => rw [fs, hs, h1]

private theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos (c : ℝ) (a b : ℂ) : (a * (c • b)).re = c * (a * b).re := by
  rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]

theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.bil_eq :
    ∀ {P : Type} [inst : Fintype P] [DecidableEq P] {n g : ℕ} (R : (P → Fin n → ℂ) ≃ₗ[ℝ] Fin g → ℂ)
      (Hm : Matrix (Fin g) (Fin g) ℂ) (M : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ) (S : Set (P → Fin n → ℂ)),
      Submodule.span ℝ S = ⊤ →
        (∀ a ∈ S,
            ∀ b ∈ S,
              (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm ((R : (P → Fin n → ℂ) → Fin g → ℂ) a) ((R : (P → Fin n → ℂ) → Fin g → ℂ) b)).im =
                ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (b v)).re) →
          ∀ (x y : P → Fin n → ℂ),
            (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm ((R : (P → Fin n → ℂ) → Fin g → ℂ) x) ((R : (P → Fin n → ℂ) → Fin g → ℂ) y)).im =
              ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (x v) (y v)).re := by
  intro P _ _ n g R Hm M s r S hS H x y
  have step : ∀ a ∈ S, ∀ y : P → Fin n → ℂ,
      (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R a) (R y)).im =
        ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (y v)).re := by
    intro a ha y
    refine UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span (fun y => (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R a) (R y)).im)
      (fun y => ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (y v)).re)
      S hS ?_ ?_ ?_ ?_ (H a ha) y
    · intro u w
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add,
        Complex.add_im]
    · intro c u
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_smul, star_smul, star_trivial, Matrix.mulVec_smul,
        dotProduct_smul, Complex.smul_im, smul_eq_mul]
    · intro u w
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.add_apply, star_add, add_dotProduct, mul_add,
        Complex.add_re, Finset.sum_add_distrib]
    · intro c u
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct,
        UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos, Finset.mul_sum, mul_left_comm c]
  refine UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span (fun x => (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R x) (R y)).im)
    (fun x => ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (x v) (y v)).re)
    S hS ?_ ?_ ?_ ?_ (fun a ha => step a ha y) x
  · intro u w
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_add, add_dotProduct, Complex.add_im]
  · intro c u
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_smul, smul_dotProduct, Complex.smul_im, smul_eq_mul]
  · intro u w
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, mul_add,
      Complex.add_re, Finset.sum_add_distrib]
  · intro c u
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul,
      UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos, Finset.mul_sum, mul_left_comm c]
