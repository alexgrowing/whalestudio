import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def archFactor (n : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))

def IsCompletedL (χ : HChar E) (n : I → ℤ) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re → ∃ L : ℂ, HasProd (eulerFactor χ s) L ∧ Λ s = archFactor n s * L

def BoundedInStrips (Λ : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C

def CompletedLBoundedInStrips : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ), IsUnitary χ → Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) →
      ∃ Λ : ℂ → ℂ, IsCompletedL χ n Λ ∧ BoundedInStrips Λ

def CompletedLBoundedInStripsEven : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ), IsUnitary χ → HasInfRatio χ φ m → (∃ i, m i ≠ 0) →
      ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
        (∀ s : ℂ, 1 < s.re → ∃ L : ℂ, HasProd (eulerFactor χ s) L ∧ Λ s = LInf m s * L) ∧ BoundedInStrips Λ

theorem IsCompletedL.unique {χ : HChar E} {n : I → ℤ} {f g : ℂ → ℂ} (hf : IsCompletedL χ n f) (hg : IsCompletedL χ n g) :
    f = g :=
  entire_eq_of_halfPlane hf.1 hg.1 1 fun s hs => by
    obtain ⟨L, h1, h2⟩ := hf.2 s hs
    obtain ⟨L', h1', h2'⟩ := hg.2 s hs
    rw [h2, h2', h1.unique h1']

theorem IsCompletedL.eq_mul {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L)
    {s : ℂ} (hs : 1 < s.re) : Λ s = archFactor n s * L s := by
  obtain ⟨L', h1, h2⟩ := h.2 s hs
  rw [h2, h1.unique (hL.2 s hs)]

theorem archFactor_two_mul (m : I → ℤ) (s : ℂ) : archFactor (fun i => 2 * m i) s = LInf m s := by
  unfold archFactor LInf
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (((|2 * m i| : ℤ) : ℂ)) / 2 = ((|m i| : ℤ) : ℂ) := by
    rw [abs_mul, abs_two]; push_cast; ring
  rw [this]

theorem CompletedLBoundedInStrips.forall (h : CompletedLBoundedInStrips) [IsTotallyComplex E] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} (hu : IsUnitary χ) (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0)
    {Λ : ℂ → ℂ} (hΛ : IsCompletedL χ n Λ) : BoundedInStrips Λ := by
  obtain ⟨Λ', h1, h2⟩ := h E I φ hφ χ n hu hi hn
  rwa [hΛ.unique h1]

theorem CompletedLBoundedInStrips.even (h : CompletedLBoundedInStrips) : CompletedLBoundedInStripsEven := by
  intro E _ _ _ I _ φ hφ χ m hu hi ⟨i, hm⟩
  obtain ⟨Λ, h1, h2⟩ := h E I φ hφ χ (fun i => 2 * m i) hu hi ⟨i, mul_ne_zero two_ne_zero hm⟩
  refine ⟨Λ, h1.1, fun s hs => ?_, h2⟩
  simpa only [archFactor_two_mul] using h1.2 s hs

example : ¬ BoundedInStrips (fun s => s) := by
  intro h
  obtain ⟨C, hC⟩ := h 0 1 one_pos
  have := hC (((|C| + 1 : ℝ) : ℂ) * Complex.I) (by simp) (by simp)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
  linarith [le_abs_self C]

example : archFactor (fun _ : Unit => (-2 : ℤ)) 0 = (Real.pi : ℂ)⁻¹ := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [archFactor, Complex.cpow_neg_one]
  field_simp

end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
