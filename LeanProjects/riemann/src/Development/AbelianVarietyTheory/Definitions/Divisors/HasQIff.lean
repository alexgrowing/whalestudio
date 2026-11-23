import Mathlib

noncomputable section

open scoped UpperHalfPlane MatrixGroups ModularForm

namespace GlobalTheory.QFam

def HasQ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f τ)

def IsFam {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) : Prop :=
  ∀ (i : ι) (γ : SL(2, ℤ)), (f i) ∣[w] γ = f (act i γ)

def IsRAct {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  (∀ i, act i 1 = i) ∧ ∀ i γ δ, act (act i γ) δ = act i (γ * δ)

def ActBij {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  ∀ γ, Function.Bijective fun i => act i γ

def FamQ {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (N : ℕ) (f : ι → ℍ → ℂ) (a : ι → ℕ → ℂ) : Prop :=
  IsFam act w f ∧ ∀ i, HasQ N (f i) (a i)

def conv (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def spread (M : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if M ∣ n then a (n / M) else 0

def QAll (p : ℂ → Prop) (N : ℕ) (f : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ ∀ n, p (a n)

def QConj (g : ℂ ≃+* ℂ) (N : ℕ) (f f' : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ HasQ N f' fun n => g (a n)

def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    have hs : s = 0 := by
      have : s * τ.im = 0 := by simpa using him
      exact (mul_eq_zero.mp this).resolve_right τ.im_pos.ne'
    subst hs
    exact ⟨rfl, by simpa using hre⟩

theorem IsRAct.actBij {ι : Type} {act : ι → SL(2, ℤ) → ι} (h : IsRAct act) : ActBij act := by
  obtain ⟨hone, hmul⟩ := h
  intro γ
  refine Function.bijective_iff_has_inverse.mpr ⟨fun i => act i γ⁻¹, fun i => ?_, fun i => ?_⟩
  · show act (act i γ) γ⁻¹ = i
    rw [hmul, mul_inv_cancel, hone]
  · show act (act i γ⁻¹) γ = i
    rw [hmul, inv_mul_cancel, hone]

theorem hasQ_iff (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n) (f τ) := by
  have key : ∀ (τ : ℍ) (n : ℕ), Complex.exp (2 * Real.pi * Complex.I * n * τ / N)
      = Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n := by
    intro τ n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [HasQ, key]

end GlobalTheory.QFam
