import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Formalism.ThetaLogCoordinates.SandwichModelDomains.StatementW

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST

def WeylPair : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
    (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ P ∈ (weyl O r n hn ν).map (toK O K), ∀ Q ∈ (dualWeyl O r n ν).map (toK O K),
      ∃ z : O, fockR P Q = algebraMap O K z * fockR (hw K hn ν) (hw K hn ν)

def DualWeylIn : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
    (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ Q ∈ dualWeyl K r n ν,
    (∀ P ∈ (weyl O r n hn ν).map (toK O K), ∃ z : O, fockR P Q = algebraMap O K z * fockR (hw K hn ν) (hw K hn ν)) →
    Q ∈ (dualWeyl O r n ν).map (toK O K)

def NondegK : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (r n : ℕ) (_hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ Q ∈ dualWeyl K r n ν,
    (∀ P ∈ dualWeyl K r n ν, fockR P Q = 0) → Q = 0

def FormCoreG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CharZero K], ¬ IsUnit ((p : ℕ) : O) →
    ∀ (r n : ℕ) (_hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∃ B : MvPolynomial (Fin r × Fin n) K →ₗ[K] MvPolynomial (Fin r × Fin n) K →ₗ[K] K,
      (∀ (g : Matrix (Fin r) (Fin r) K) (P Q : MvPolynomial (Fin r × Fin n) K),
        B (rowAct K g P) Q = B P (rowAct K g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl K r n ν, (∀ P ∈ dualWeyl K r n ν, B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl K r n ν,
        (∀ P ∈ (dualWeyl O r n ν).map (toK O K), B P Q ∈ Set.range (algebraMap O K)) → Q ∈ (dualWeyl O r n ν).map (toK O K)) ∧
      (∀ l : ℕ, LBound r ν l → ∀ Q ∈ (dualWeyl O r n ν).map (toK O K), ∀ P ∈ (dualWeyl O r n ν).map (toK O K),
        B P (((p : K) ^ sExp p r l) • Q) ∈ Set.range (algebraMap O K)) ∧
      ((∀ t, ν t = 0) → ∀ Q ∈ (dualWeyl O r n ν).map (toK O K), ∀ P ∈ (dualWeyl O r n ν).map (toK O K),
        B P Q ∈ Set.range (algebraMap O K))

end Formalism.L2.G.Model.TS
