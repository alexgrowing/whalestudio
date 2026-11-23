import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt

namespace GlobalTheory.Published

def ConjInv {K : Type} [Field K] {m : ℕ} (h : HermFam K (Fin m → K)) : Prop :=
  ∀ (σ : K →+* ℂ) x y, h.form ((starRingEnd ℂ).comp σ) x y = starRingEnd ℂ (h.form σ x y)

def AbsoluteSiegel : Prop := ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (h : HermFam K (Fin m → K))
  (L : Submodule (𝓞 K) (Fin m → K)), 1 ≤ m → ConjInv h → Full L → ∀ ε : ℝ, 0 < ε →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (h' : HermFam K' (Fin m → K')) (x : Fin m → K'),
      IsBC h h' ∧ x ≠ 0 ∧ deg h L / m - Real.log m / 2 - ε ≤ deg h' (lineLat (latBC K' L) x)

end GlobalTheory.Published
