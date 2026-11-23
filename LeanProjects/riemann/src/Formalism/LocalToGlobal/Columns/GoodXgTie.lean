import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXg
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section Comparison₂

variable {X : Fields} (Pr : Primes X) {m : ℕ} (Ch : Chars X Pr m) (r : ℕ) [∀ i, Fact (Pr.g i).Prime]
  (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ) (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i))

def XgGreenOk : Prop :=
  ∀ i : Fin 2, (∀ x y : Formalism.CyclotomicNorms.Fbar (Pr.g i), x ≠ 0 → y ≠ 0 → teich i x = teich i y → x = y) ∧
    Formalism.L2.NT.IsGenSys (ζ i)

def gxGoodIrrC : Set (G0 X.E Pr.vGs r → ℂ) :=
  {χc | Formalism.L2.NT.IsIrrChar χc ∧ gxGood Pr Ch r σ teich ζ χc}

def XgCTie : Prop :=
  (∃ z : X.K, IsPrimitiveRoot z (Fintype.card (G0 X.E Pr.vGs r))) →
    (((XgC Pr Ch r σ teich ζ).image fun χ x => σ (χ x) : Finset (G0 X.E Pr.vGs r → ℂ)) : Set (G0 X.E Pr.vGs r → ℂ)) =
      gxGoodIrrC Pr Ch r σ teich ζ

def XgNonempty : Prop := Pr.Ok → Ch.Ok → XgGreenOk Pr teich ζ → (∀ i, 3 ≤ Pr.g i) → 9 ≤ r → 2 ≤ X.f →
  (∃ z : X.K, IsPrimitiveRoot z (Fintype.card (G0 X.E Pr.vGs r))) → (XgC Pr Ch r σ teich ζ).Nonempty

end Comparison₂

end Formalism.L2.Col
