import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def ValuationProperties (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  vK p (0 : KK O) = ⊤ ∧
  (∀ x y : KK O, vK p (x * y) = vK p x + vK p y) ∧
  (∀ x y : KK O, min (vK p x) (vK p y) ≤ vK p (x + y)) ∧
  (∀ m : ℕ, m ≠ 0 → vK p (m : KK O) = ((padicValNat p m : ℚ) : WithTop ℚ)) ∧
  (∀ x : KK O, vK p (-x) = vK p x) ∧
  (∀ x : KK O, 0 ≤ vK p x ↔ ∃ o : O, x = algebraMap O (KK O) o)

def FockLatticeClosure (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ σ : Type,
    InBB (O := O) p (0 : MvPolynomial σ (KK O)) ∧
    (∀ F G : MvPolynomial σ (KK O), InBB (O := O) p F → InBB (O := O) p G → InBB (O := O) p (F + G)) ∧
    (∀ (o : O) (F : MvPolynomial σ (KK O)), InBB (O := O) p F → InBB (O := O) p (o • F)) ∧
    (∀ (m : σ →₀ ℕ) (c : KK O), InBB (O := O) p (monomial m c) ↔
      0 ≤ vK p c + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)) ∧
    (∀ F : MvPolynomial σ (KK O), InBB (O := O) p F ↔ ∀ m, InBB (O := O) p (monomial m (F.coeff m))) ∧
    (∀ u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O),
      (∀ m c, InBB (O := O) p (monomial m c) → InBB (O := O) p (u (monomial m c))) →
      ∀ F, InBB (O := O) p F → InBB (O := O) p (u F)) ∧
    (∀ (m m' : σ →₀ ℕ) (c : KK O) (z : ℤ), InBB (O := O) p (monomial m c) →
      (z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) →
      InBB (O := O) p (monomial m' (c * (z : KK O)))) ∧
    (∀ u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O),
      (∀ m, u (monomial m 1) ∈ IntPol O σ) → ∀ F ∈ IntPol O σ, u F ∈ IntPol O σ) ∧
    (∀ (m : σ →₀ ℕ) (z : ℤ), monomial m (z : KK O) ∈ IntPol O σ) ∧
    (∀ F : MvPolynomial σ (KK O), F ∈ IntPol O σ ↔ ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o)

def PolynomialIntegralFormPreservesLattices (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι),
    PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)

def IntegralFormGeneratorsPreserveLattices (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι), ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)

def FockLatticeFiniteSpanning (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι],
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
