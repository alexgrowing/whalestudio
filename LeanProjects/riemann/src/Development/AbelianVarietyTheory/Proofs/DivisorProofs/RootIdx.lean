import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.CovTest

namespace GlobalTheory.BcEigen

section Model

variable {ι : Type} [Fintype ι] (r : ι → ℕ)

def sq2 : MvPolynomial (Σ a, Fin (r a)) ℝ := ∑ z, X z ^ 2

def eSum (a : ι) : MvPolynomial (Σ a, Fin (r a)) ℝ := ∑ i : Fin (r a), X (⟨a, i⟩ : Σ a, Fin (r a))

def linE (s : ι → ℝ) : MvPolynomial (Σ a, Fin (r a)) ℝ := ∑ a, C (s a) * eSum r a

def monPt (a : ι) : MvPolynomial (Σ a, Fin (r a)) ℝ :=
  ∏ i : Fin (r a), (-X (⟨a, i⟩ : Σ a, Fin (r a))) ^ (r a - 1 - (i : ℕ))

def vdm (a : ι) : MvPolynomial (Σ a, Fin (r a)) ℝ :=
  ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (X (⟨a, i'⟩ : Σ a, Fin (r a)) - X ⟨a, i⟩)

end Model

def rootIdx (ι : Type) (N j : ℕ) (x : ι × Fin N) : Σ a : ι × Bool, Fin (rkB ι N j a) :=
  if h : (x.2 : ℕ) < j then ⟨(x.1, true), ⟨x.2, h⟩⟩
  else ⟨(x.1, false), ⟨(x.2 : ℕ) - j, by show (x.2 : ℕ) - j < N - j; have := x.2.isLt; omega⟩⟩

def lamSign {ι : Type} (a : ι × Bool) : ℝ := cond a.2 (-1) 1

example : rootIdx Unit 3 1 ((), 0) = ⟨((), true), ⟨0, by simp [rkB]⟩⟩ := by simp [rootIdx]

example : rootIdx Unit 3 1 ((), 2) = ⟨((), false), ⟨1, by simp [rkB]⟩⟩ := by
  simp [rootIdx]

end GlobalTheory.BcEigen

end
