import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrassTop

def wt {ι : Type} (d : ι × ℕ →₀ ℕ) : ℕ := d.sum fun x i => x.2 * i

def rel (k : ℕ) : MvPolynomial (Bool × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (true, a) * X (false, k - a)

def gens (p q : ℕ) : Set (MvPolynomial (Bool × ℕ) ℝ) :=
  {f | (∃ k, 1 ≤ k ∧ f = rel k) ∨ (∃ b, f = X (b, 0) - 1) ∨ (∃ k, p < k ∧ f = X (true, k)) ∨
    (∃ k, q < k ∧ f = X (false, k))}

def J (p q : ℕ) : Ideal (MvPolynomial (Bool × ℕ) ℝ) := Ideal.span (gens p q)

def basis (p q : ℕ) : Set (MvPolynomial (Bool × ℕ) ℝ) :=
  {f | (∃ d, wt d < p * q ∧ f = monomial d 1) ∨ f = X (true, p) ^ q}

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def renVar {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (y : Bool × ℕ) : (E →+* ℂ) × ℕ :=
  (if y.1 then τ.1 else conjEmb τ.1, y.2)

def ren {H : Host E} (τ : GlobalTheory.AllWt.Psi H) :
    MvPolynomial (Bool × ℕ) ℝ →ₐ[ℝ] MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  rename (renVar τ)

end GlobalTheory.GrassTop
