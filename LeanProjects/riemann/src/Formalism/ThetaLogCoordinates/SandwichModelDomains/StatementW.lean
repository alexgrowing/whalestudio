import Formalism.GradedWeylDivisibility.StatementA

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

def sExp (p r l : ℕ) : ℕ := r * (r - 1) / 2 * Nat.log p (l + r - 1)

def LBound (r : ℕ) {n : ℕ} (ν : Fin n → ℕ) (l : ℕ) : Prop :=
  (∀ t, ν t ≤ l) ∨ (n = r ∧ ∀ s t, ν s ≤ ν t + l)

def PrimeToPUnits (p : ℕ) (O : Type) [CommRing O] : Prop :=
  ∀ c : ℤ, ¬ (p : ℤ) ∣ c → IsUnit ((c : ℤ) : O)

def SandwichZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ x ∈ dualWeyl ℤ_[p] r n ν, ((p : ℤ_[p]) ^ sExp p r l) • x ∈ weyl ℤ_[p] r n hn ν

def SandwichZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ f ∈ dualWeyl ℤ r n ν, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ (c * (p : ℤ) ^ sExp p r l) • f ∈ weyl ℤ r n hn ν

def SandwichDomain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ (O : Type) [CommRing O] [IsDomain O], PrimeToPUnits p O →
      (∀ x ∈ dualWeyl O r n ν, ((p : O) ^ sExp p r l) • x ∈ weyl O r n hn ν) ∧
      weyl O r n hn ν ≤ dualWeyl O r n ν

def UnitsOfLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O], ¬ IsUnit ((p : ℕ) : O) → PrimeToPUnits p O

def SandwichLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], ¬ IsUnit ((p : ℕ) : O) →
      (∀ x ∈ dualWeyl O r n ν, ((p : O) ^ sExp p r l) • x ∈ weyl O r n hn ν) ∧
      weyl O r n hn ν ≤ dualWeyl O r n ν

def SandwichModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf], PrimeToPUnits p O →
    ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      (∀ x ∈ Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
          (dualWeyl O (m + 1) (m + 1) fun t => (lam t - lam (Fin.last m)).toNat),
        ((p : O) ^ ((m + 1) * (m + 1 - 1) / 2 * Nat.log p ((lam 0 - lam (Fin.last m)).toNat + (m + 1) - 1))) • x ∈
          Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
            (weyl O (m + 1) (m + 1) le_rfl fun t => (lam t - lam (Fin.last m)).toNat)) ∧
      Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
          (weyl O (m + 1) (m + 1) le_rfl fun t => (lam t - lam (Fin.last m)).toNat) ≤
        Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
          (dualWeyl O (m + 1) (m + 1) fun t => (lam t - lam (Fin.last m)).toNat)

def SandwichModelLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O Kf : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Kf] [Algebra O Kf],
    ¬ IsUnit ((p : ℕ) : O) →
    ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
      (∀ x ∈ Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
          (dualWeyl O (m + 1) (m + 1) fun t => (lam t - lam (Fin.last m)).toNat),
        ((p : O) ^ ((m + 1) * (m + 1 - 1) / 2 * Nat.log p ((lam 0 - lam (Fin.last m)).toNat + (m + 1) - 1))) • x ∈
          Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
            (weyl O (m + 1) (m + 1) le_rfl fun t => (lam t - lam (Fin.last m)).toNat)) ∧
      Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
          (weyl O (m + 1) (m + 1) le_rfl fun t => (lam t - lam (Fin.last m)).toNat) ≤
        Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
          (dualWeyl O (m + 1) (m + 1) fun t => (lam t - lam (Fin.last m)).toNat)

end Formalism.InvariantFactorPaths.INST
