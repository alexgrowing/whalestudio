import Mathlib
noncomputable section
namespace GlobalTheory.BI

def IsChar (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] (χ : G → L) : Prop :=
  ∃ (n : ℕ) (ρ : Representation K G (Fin n → K)), ∀ g, χ g = algebraMap K L (ρ.character g)

def IsIrrChar (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] (χ : G → L) : Prop :=
  ∃ (n : ℕ) (ρ : Representation K G (Fin n → K)), ρ.IsIrreducible ∧ ∀ g, χ g = algebraMap K L (ρ.character g)

def Virt (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] : AddSubgroup (G → L) :=
  AddSubgroup.closure {χ | IsChar K L χ}
open Classical in

def ext0 {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L) (g : G) : L :=
  if h : g ∈ H then ψ ⟨g, h⟩ else 0

def ind {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L) (g : G) : L :=
  (Nat.card H : L)⁻¹ * ∑ᶠ x : G, ext0 H ψ (x⁻¹ * g * x)

def pair {L G : Type} [Field L] [Group G] (a b : G → L) : L :=
  (Nat.card G : L)⁻¹ * ∑ᶠ g : G, a g * b g⁻¹

def AbByP (G : Type) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ A : Subgroup G, A.Normal ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ A

theorem isChar_one (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] :
    IsChar K L (fun _ : G => (1 : L)) := by
  refine ⟨1, Representation.trivial K G (Fin 1 → K), fun g => ?_⟩
  simp [Representation.character, Representation.trivial]

end GlobalTheory.BI
