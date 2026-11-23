import Mathlib
import Formalism.PeriodIntegrals.MiracleFlat

universe u

namespace PI.UnitaryGroupMassFormula.MF

open RingTheory.Sequence IsLocalRing

def RegSeqGen : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A],
    ∃ xs : List A, IsRegular A xs ∧ Ideal.ofList xs = maximalIdeal A ∧ (xs.length : WithBot ℕ∞) = ringKrullDim A

def AssDim : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R), IsRegular M rs → ∀ p ∈ associatedPrimes R M, (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)

def DepthDrop : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (x : R), IsRegular M rs → rs ≠ [] → x ∈ maximalIdeal R → IsSMulRegular M x →
      ∃ zs : List R, zs.length + 1 = rs.length ∧ IsRegular (QuotSMulTop x M) zs

def CMSop : Prop :=
  ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B],
    (∃ rs : List B, IsRegular B rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal B) ∧ (rs.length : WithBot ℕ∞) = ringKrullDim B) →
    ∀ xs : List B, (∀ x ∈ xs, x ∈ maximalIdeal B) →
      ringKrullDim B = (xs.length : WithBot ℕ∞) + ringKrullDim (B ⧸ Ideal.ofList xs) → IsRegular B xs

def CMSopOf : Prop := AssDim.{u} → DepthDrop.{u} → CMSop.{u}

def LocCrit : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B] (x : A),
    IsSMulRegular A x → IsSMulRegular B (algebraMap A B x) → algebraMap A B x ∈ maximalIdeal B →
    Module.Flat (A ⧸ Ideal.span {x}) (B ⧸ (Ideal.span {x}).map (algebraMap A B)) → Module.Flat A B

def FlatOfReg : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (xs : List A), IsRegular A xs → Ideal.ofList xs = maximalIdeal A →
    IsRegular B (xs.map (algebraMap A B)) → Module.Flat A B

def FlatOfRegOf : Prop := LocCrit.{u} → FlatOfReg.{u}

def Assembly : Prop := RegSeqGen.{u} → CMSop.{u} → FlatOfReg.{u} → PI.MiracleFlat.{u}

end PI.UnitaryGroupMassFormula.MF
