import Mathlib

noncomputable section

namespace UpperTheory.Gal.Gen

def HB : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (X : Type) [Fintype X] (P : Submodule k (X → k)) (v : X → k) (r : ℝ),
    (∀ a : X → k, (∀ i, ‖a i‖ ≤ 1) → (∀ c ∈ P, ∑ i, a i * c i = 0) → ‖∑ i, a i * v i‖ ≤ r) → ∃ c ∈ P, ∀ i, ‖v i - c i‖ ≤ r

def DetLow : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (N : ℕ) (A B : Matrix (Fin N) (Fin N) k) (c : k) (ρ : ℕ),
    (∀ i j, ‖A i j‖ ≤ 1) → (∀ i j, ‖B i j‖ ≤ 1) → ‖c‖ ≤ 1 → A.rank ≤ ρ → ‖(A + c • B).det‖ ≤ ‖c‖ ^ (N - ρ)

def FixVec : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H : Type) [Group H], IsPGroup l H → ∀ (V : Type) [AddCommGroup V] [Module (ZMod l) V] [Finite V]
    (ρ : Representation (ZMod l) H V) (U : Submodule (ZMod l) V), (∀ h, ∀ u ∈ U, ρ h u ∈ U) → U ≠ ⊤ →
    ∃ v, v ∉ U ∧ ∀ h, ρ h v - v ∈ U

def Flag : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H : Type) [Group H], IsPGroup l H → ∀ (V : Type) [AddCommGroup V] [Module (ZMod l) V] [Finite V]
    (ρ : Representation (ZMod l) H V),
    ∃ b : Module.Basis (Fin (Module.finrank (ZMod l) V)) (ZMod l) V, ∀ h i j, j ≤ i → b.repr (ρ h (b j) - b j) i = 0

def TriMat : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (H : Type) [Group H], IsPGroup l H → ∀ (X : Type) [Fintype X] [DecidableEq X]
    (ρ : H →* Matrix X X ℤ), ∃ (Q : Matrix (Fin (Fintype.card X)) X ℤ) (P : Matrix X (Fin (Fintype.card X)) ℤ),
      ∀ h i j, j ≤ i → (l : ℤ) ∣ (Q * ρ h * P) i j - (if i = j then 1 else 0)

def GroupDet : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (l : ℕ) [Fact l.Prime] (H : Type) [Group H] [Fintype H], IsPGroup l H →
    ∀ (a : H → k) (ρ : ℕ), (∀ h, ‖a h‖ ≤ 1) → (Matrix.of fun h g : H => a (h * g⁻¹)).rank ≤ ρ →
    ‖∑ h, a h‖ ^ Fintype.card H ≤ ‖(l : k)‖ ^ (Fintype.card H - ρ)

def Alg : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (l : ℕ) [Fact l.Prime] (H : Type) [Group H] [Fintype H], IsPGroup l H →
    ∀ P : Submodule k (H → k), (∀ c ∈ P, ∀ g, (fun h => c (h * g)) ∈ P) → Fintype.card H ≤ 2 * Module.finrank k P →
    ∃ c ∈ P, ∀ h, ‖1 - c h‖ ^ 2 ≤ ‖(l : k)‖

def Codim : Prop :=
  ∀ (k V M : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup M] [Module k M]
    (Ψ : V →ₗ[k] M) (A B : Submodule k M) [FiniteDimensional k B], (∀ v, Ψ v ∈ A ⊔ B) →
    Module.finrank k V ≤ Module.finrank k (A.comap Ψ) + Module.finrank k B

def HS : Prop :=
  ∀ (X : Type) [Fintype X] (B : Matrix X X ℂ) (V : Submodule ℂ (X → ℂ)), (∀ v ∈ V, B.mulVec v = v) →
    (Module.finrank ℂ V : ℝ) ≤ ∑ x, ∑ y, ‖B x y‖ ^ 2

end UpperTheory.Gal.Gen

end
