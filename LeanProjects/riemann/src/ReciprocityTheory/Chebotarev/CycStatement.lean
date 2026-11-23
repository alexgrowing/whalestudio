import Mathlib

open NumberField

namespace ReciprocityTheory.Cheb

def Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (σ : Gal(K/ℚ)) (T : Finset ℕ),
    ∃ p : ℕ, p.Prime ∧ p ∉ T ∧ ∃ P : Ideal (𝓞 K), ∃ _ : P.IsPrime,
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ Algebra.IsUnramifiedAt ℤ P ∧ IsArithFrobAt ℤ σ P

def CycStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∀ (a : (ZMod l)ˣ) (T : Finset ℕ), ∃ q : Ideal (𝓞 E), q.IsPrime ∧ (Ideal.absNorm q).Prime ∧ Ideal.absNorm q ∉ T ∧
      ((Ideal.absNorm q : ℕ) : ZMod l) = a

end ReciprocityTheory.Cheb
