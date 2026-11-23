import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LowerSetTypesSpan
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.IntegralJointTypeSum

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

def GlOperatorsFormRepresentation : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k),
    Function.Injective e → IsGLRep (glOpsE F LL S e)

def IsotypicZeroOfNonDominant : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k),
    Function.Injective e → ∀ a : Fin m → ℤ, ¬ Dominant a → isoSub (glOpsE F LL S e) a = ⊥

def ProjectorsPreserveMultidegree : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k),
    Function.Injective e → ∀ pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F),
    DecSys (isoSub (glOpsE F LL S e)) pr → ∀ (B : Fin N → ℕ) (a : Fin m → ℤ), ∀ x ∈ Pol F k B, pr a x ∈ Pol F k B

def TypeSumsByEvaluation : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S : Set (Fin N)) (e : Fin m → Fin k)
    (dcd : Fin k → Option (Fin m)), (∀ a, dcd (e a) = some a) → (∀ c a, dcd c = some a → c = e a) →
    ∀ (pi : Set (Fin m → ℤ)) (x : MvPolynomial (Fin N × Fin k) F),
    (x ∈ ⨆ a ∈ pi, isoSub (glOpsE F LL S e) a) ↔ ∀ y, Tev dcd y x ∈ ⨆ a ∈ pi, isoSub (glOps F m LL S) a

def ProjectorsCommuteNested : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m k : ℕ) (LL : Letters (Fin N)) (S S' : Set (Fin N)) (e : Fin m → Fin k),
    Function.Injective e → (S ⊆ S' ∨ S' ⊆ S) →
    ∀ pr pr' : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F),
    DecSys (isoSub (glOpsE F LL S e)) pr → DecSys (isoSub (glOpsE F LL S' e)) pr' →
    ∀ a b, pr a * pr' b = pr' b * pr a

def ProjectorsCommuteDisjoint : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N m m' k : ℕ) (LL : Letters (Fin N)) (S S' : Set (Fin N))
    (e : Fin m → Fin k) (e' : Fin m' → Fin k), Function.Injective e → Function.Injective e' →
    (∀ a a', e a ≠ e' a') →
    ∀ (pr : (Fin m → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F))
      (pr' : (Fin m' → ℤ) → Module.End F (MvPolynomial (Fin N × Fin k) F)),
    DecSys (isoSub (glOpsE F LL S e)) pr → DecSys (isoSub (glOpsE F LL S' e')) pr' →
    ∀ a b, pr a * pr' b = pr' b * pr a

def ExternalProductBasis : Prop :=
  ∀ (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ),
    LinearIndependent R (pvec R r K LL B) ∧ Submodule.span R (Set.range (pvec R r K LL B)) = Pol R (r + K) B

def RestLowPl : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : Fin (N + 1))
    (pi : Set (Fin r → ℤ)), DomLowerSet pi →
    Pol F (r + K) B ⊓ (⨆ a ∈ pi, isoSub (glOpsE F LL {j | j.val < i.val} (Fin.castAdd K)) a) =
      Submodule.span F (pvec F r K LL B '' {x | x.1.1.1 i ∈ pi})

def RestLowTan : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : Fin (N + 1))
    (pi : Set (Fin K → ℤ)), DomLowerSet pi →
    Pol F (r + K) B ⊓ (⨆ a ∈ pi, isoSub (glOpsE F LL {j | j.val < i.val} (Fin.natAdd r)) a) =
      Submodule.span F (pvec F r K LL B '' {x | x.1.2.1 i ∈ pi})

end Formalism.MainNotions.G.ColumnFamilies
