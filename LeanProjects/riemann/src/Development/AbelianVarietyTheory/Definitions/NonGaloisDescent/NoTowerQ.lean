import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import GroundTheory.LocalFields.UpperNumbering

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField

namespace GlobalTheory.PMon.Ram

open Classical in

def jumpSum {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) : ℕ :=
  ∑ᶠ t : ℕ, if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)

section

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def wild (t : ℕ) : Subgroup (L ≃ₐ[K] L) := lowerRamificationGroup K L ((t : ℤ) + 1)

def AxIn (p : ℕ) : Prop :=
  ∀ (J : Subgroup (L ≃ₐ[K] L)) (x : L), (∀ σ ∈ J, σ x - x ∈ 𝒪[L]) →
    ∃ y : L, (∀ σ ∈ J, σ y = y) ∧ (p : L) ^ 2 * (x - y) ∈ 𝒪[L]

variable {K L} in

def Detects (p r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)) : Prop :=
  ∀ σ₀ ∈ A, σ₀ ∉ B → ∃ (x : L) (a : (L ≃ₐ[K] L) → ℤ),
    (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) ∧ ¬ (p : ℤ) ^ r ∣ a σ₀

end

def OrdIs (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] (p E : ℕ) : Prop :=
  IsDiscreteValuationRing.addVal 𝒪[L] (p : 𝒪[L]) = (E : ℕ∞)

def NoTower : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (N : ℕ → Subgroup ↥(GK K)), Antitone N →
    (∀ k, IsOpen (N k : Set ↥(GK K))) →
    (∀ k, ∀ σ ∈ N k, σ ^ l ∈ N (k + 1)) →
    (∀ j, ∀ σ ∈ N 0, σ ^ l ∈ N (j + 1) → σ ∈ N j) →
    (∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → ℂ_[l]) (a : ι → ↥(GK K) → ℤ_[l]),
      (∀ i, ∀ σ ∈ N k, ‖Formalism.Per.σC (σ : GQ l) (x i) - x i - algebraMap ℚ_[l] ℂ_[l] (a i σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧
      ∀ σ ∈ N k, (∀ i, (l : ℤ_[l]) ^ r ∣ a i σ) → σ ∈ N (k + r)) →
    ∃ k, ∀ j, IK K ⊓ N k ≤ N j

def NoTowerQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N : ℕ → Subgroup (GQ l)), Antitone N →
    (∀ k, IsOpen (N k : Set (GQ l))) →
    (∀ k, ∀ σ ∈ N k, σ ^ l ∈ N (k + 1)) →
    (∀ j, ∀ σ ∈ N 0, σ ^ l ∈ N (j + 1) → σ ∈ N j) →
    (∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → Om l) (a : ι → GQ l → ℤ),
      (∀ i, ∀ σ ∈ N k, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧
      ∀ σ ∈ N k, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N (k + r)) →
    ∃ k, ∀ j, ∀ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → σ ∈ N j

end GlobalTheory.PMon.Ram

end
