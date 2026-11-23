import ReciprocityTheory.DualLattices.CotangentSurjective

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def PrimeHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ AA : HopfOrder (C := C) R (ZMod p),
    ∃ (x ω : ZMod p → C) (δ : R),
      x ∈ AA.carrier ∧ x 0 = 0 ∧ (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      (∀ a, x a = ω a * x 1) ∧ x ^ p = (fun a => algebraMap R C δ * x a) ∧
      v (algebraMap R C δ) = v (x 1) ^ (p - 1) ∧
      AA.carrier = Submodule.span R (Set.range fun j : Fin p => x ^ (j : ℕ)) ∧
      augIdeal AA.carrier = Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j} ∧
      sqIdeal (augIdeal AA.carrier) = Submodule.span R
        ({fun a => algebraMap R C δ * x a} ∪ {y | ∃ j : ℕ, 2 ≤ j ∧ j < p ∧ y = x ^ j}) ∧
      HasColen R v AA.carrier (v (x 1) ^ (p * (p - 1) / 2))

end ReciprocityTheory.PGsh.Up
