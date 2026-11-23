import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow

noncomputable section

open CategoryTheory NumberField
open scoped TensorProduct

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V.KH

def FgShift : Prop :=
  ∀ (G : Type) [Group G] (A s m : ℕ) (X : ℕ → Type) [∀ p, MulAction G (X p)]
    (d : ∀ p, permRep G (X (p + 1)) ⟶ permRep G (X p)) (M : Rep ℤ G) (e : permRep G (X 0) ⟶ M),
    1 ≤ s → Function.Surjective e.hom → Function.Exact (d 0).hom e.hom →
    (∀ p, p < m → Function.Exact (d (p + 1)).hom (d p).hom) →
    (∀ p, p ≤ m → OrbLe G (X p) A) → (∀ p, p ≤ m → StabLe G (X p) s) →
    Module.Finite ℤ (groupHomology M m)

def HglFG : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N m : ℕ, Module.Finite ℤ (UpperTheory.V.K.HGL L N m)

def TorsOfRank : Prop :=
  ∀ (A H : Type) [AddCommGroup A] [AddCommGroup H], AddGroup.FG H → ∀ (f : A →+ H) (R : ℕ), R ≠ 0 →
    (∀ x, f x = 0 → R • x = 0) → Module.finrank ℤ A = 0 → ∀ x : A, ∃ n : ℕ, n ≠ 0 ∧ n • x = 0

def TensTorsion : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A], (∀ x : A, ∃ n : ℕ, n ≠ 0 ∧ n • x = 0) →
    ∀ y : ℤ_[l] ⊗[ℤ] A, ∃ c : ℤ_[l], c ≠ 0 ∧ c • y = 0

end UpperTheory.FiniteGenerationAndTorsion

end
