import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestSplit
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.PolBridge

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints

def RestTypes : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N : ℕ) (LL : Letters (Fin N)) (n : ℕ) (S : Set (Fin N))
    (pi : Set (Fin n → ℤ)), DomLowerSet pi → ∀ G : MvPolynomial (Fin N × Fin n) F,
    (G ∈ ⨆ lam ∈ pi, isoSub (glOps F n LL S) lam) ↔
      ∀ mu ∈ polWts LL S (polGenSub F LL S G), Dominant mu → mu ∈ pi

def LowerSetTypesSpan : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N n : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : Fin (N + 1))
    (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    Pol F n B ⊓ (⨆ lam ∈ pi, isoSub (glOps F n LL {l | l.val < i.val}) lam) =
      Submodule.span F {H | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ P.mu i ∈ pi ∧
        H = Psi F P.mu I}

structure JointData (K V : Type) [Field K] [AddCommGroup V] [Module K V] (κ : Type) (Λ : κ → Type) (X : Type) where
  le : ∀ i, Λ i → Λ i → Prop
  dom : ∀ i, Λ i → Prop
  le_refl : ∀ i a, le i a a
  le_trans : ∀ i a b c, le i a b → le i b c → le i a c
  le_antisymm : ∀ i a b, le i a b → le i b a → a = b
  W : ∀ i, Λ i → Submodule K V
  e : ∀ i, Λ i → Module.End K V
  sys : ∀ i, DecSys (W i) (e i)
  comm : ∀ i j a b, e i a * e j b = e j b * e i a
  bot : ∀ i a, ¬ dom i a → W i a = ⊥
  Pl : Submodule K V
  stab : ∀ i a, ∀ x ∈ Pl, e i a x ∈ Pl
  b : X → V
  P : X → ∀ i, Λ i
  Pdom : ∀ x i, dom i (P x i)
  li : LinearIndependent K b
  span : Submodule.span K (Set.range b) = Pl
  low : ∀ i (pi : Set (Λ i)), (∀ a ∈ pi, dom i a) → (∀ a ∈ pi, ∀ c, dom i c → le i c a → c ∈ pi) →
    Pl ⊓ (⨆ a ∈ pi, W i a) = Submodule.span K (b '' {x | P x i ∈ pi})

def RestJointDim : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (κ : Type) [Fintype κ] [Nonempty κ] (Λ : κ → Type)
    (X : Type) [Finite X] (J : JointData K V κ Λ X) (lam : ∀ i, Λ i),
    Module.finrank K ↥(J.Pl ⊓ ⨅ i, J.W i (lam i)) = Nat.card {x // J.P x = lam}

def RestJointSum : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (κ : Type) [Fintype κ] [Nonempty κ] (Λ : κ → Type)
    (X : Type) [Finite X] (J : JointData K V κ Λ X) (pi : ∀ i, Set (Λ i)),
    (∀ i, ∀ a ∈ pi i, J.dom i a) → (∀ i, ∀ a ∈ pi i, ∀ c, J.dom i c → J.le i c a → c ∈ pi i) →
    J.Pl ⊓ (⨆ q ∈ {q : ∀ i, Λ i | ∀ i, q i ∈ pi i}, ⨅ i, J.W i (q i)) =
      Submodule.span K (J.b '' {x | ∀ i, J.P x i ∈ pi i})

end Formalism.MainNotions.G.ColumnFamilies
