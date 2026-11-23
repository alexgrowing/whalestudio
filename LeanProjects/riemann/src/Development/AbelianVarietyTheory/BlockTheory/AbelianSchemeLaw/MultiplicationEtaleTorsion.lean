import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Imports

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationEtaleTorsion

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

def translDiffPow (A : Over S) [GrpObj A] (L : LB A.left) (N : ℕ) {T : Over S} (x : T ⟶ A) :
    LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(translPt A x).left, (snd T A).left] ![(N : ℤ), -(N : ℤ)]

def MemK (A : Over S) [GrpObj A] (L : LB A.left) (N : ℕ) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    ∃ c : LB.Gen ((translDiffPow A L N x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen

def mulPullDiff (A : Over S) [GrpObj A] (L : LB A.left) (n : ℕ) : LB A.left :=
  LB.LinComb L (K := Fin 2) ![(mulN A n).left, 𝟙 A.left] ![1, -((n : ℤ) ^ 2)]

def KPowEqTorsion : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (N : ℕ), 1 ≤ N →
    ∀ (T : Over S) (x : T ⟶ P.A), MemK P.A P.L N x ↔ x ^ N = 1

def MulPullIso : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ),
    ∃ c : LB.Gen (mulPullDiff P.A P.L n), c.IsGen

def MulFiniteFlatOnto : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
    IsFinite (mulN P.A n).left ∧ Flat (mulN P.A n).left ∧ Surjective (mulN P.A n).left

def MulEtale : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
    IsUnit (n : Γ(S, ⊤)) →
    (IsFinite (mulN P.A n).left ∧ Etale (mulN P.A n).left ∧ Surjective (mulN P.A n).left ∧
      ∀ a : P.A.left, (mulN P.A n).left.finrank a = n ^ (2 * P.g)) ∧
    (IsFinite (torsion P.A n).hom ∧ Etale (torsion P.A n).hom ∧
      ∀ s : S, (torsion P.A n).hom.finrank s = n ^ (2 * P.g))

def TorsionCard : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S), (n : K) ≠ 0 →
      Nat.card {y : Over.mk s ⟶ P.A // y ^ n = 1} = n ^ (2 * P.g)

def MulMorphism : Prop := MulFiniteFlatOnto ∧ MulEtale ∧ TorsionCard

def Laws : Prop := KPowEqTorsion ∧ MulPullIso ∧ MulMorphism

theorem comp_mulN (A : Over S) [GrpObj A] {T : Over S} (x : T ⟶ A) (n : ℕ) :
    x ≫ mulN A n = x ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [pow_succ, ← ih]; simp [mulN, Hom.mul_def, comp_lift_assoc]

example (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S} (x : T ⟶ A) :
    translDiffPow A L 1 x = translDiff A L x := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationEtaleTorsion
