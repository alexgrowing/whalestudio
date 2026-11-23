import Formalism.SharpRestriction.GrowthBounds.ObjPol

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G

def TypeBound : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι)
    (e : (Fin n → ℤ) → Module.End K (MvPolynomial (ι × Fin n) K)),
    (∀ mu, IsIsoProj (glOps K n LL S) mu (e mu)) →
    (∀ G : MvPolynomial (ι × Fin n) K, ∃ T : Finset (Fin n → ℤ),
      G = ∑ mu ∈ T, e mu G ∧ ∀ mu, e mu G ∈ isoSub (glOps K n LL S) mu) →
    ∀ (G : MvPolynomial (ι × Fin n) K) (lam : Fin n → ℤ), e lam G ≠ 0 →
      (∀ M : ℤ, lam1S LL S G ≤ (M : WithBot ℤ) → lam 0 ≤ M) ∧
      (∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → th ≤ lam (lastIdx n))

end Formalism.MainNotions.TestSideWords
