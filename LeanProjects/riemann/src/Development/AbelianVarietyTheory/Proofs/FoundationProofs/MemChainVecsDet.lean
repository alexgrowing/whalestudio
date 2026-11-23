import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed

noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp TensorProduct
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def IsUnram (ν : ℚ_[g]ˣ →* ℂˣ) : Prop :=
  ∀ u : ℤ_[g]ˣ, ν (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1

def MapsToProd {n a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W') : Prop :=
  n = a + b ∧ ∃ (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W'), IsUnram ν₁ ∧ IsUnram ν₂ ∧ Λ ≠ 0 ∧
    ∀ (p : GL (Fin n) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
    (∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) →
    (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j) →
    (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) (a + i) (a + j)) →
    ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
      TensorProduct.map (σ x) (ρ y) (Λ v)

abbrev GLRep (g : ℕ) [Fact g.Prime] : Type 1 := Σ n : ℕ, Rep.{0} ℂ (GL (Fin n) ℚ_[g])

inductive InInd : GLRep g → List (GLRep g) → Prop
  | nil (π : GLRep g) : π.1 = 0 → IsIrrRep π.2.ρ → InInd π []
  | cons (π σ ρ : GLRep g) (S : List (GLRep g)) : IsIrrRep π.2.ρ → IsIrrRep ρ.2.ρ → InInd σ S →
      MapsToProd π.2.ρ σ.2.ρ ρ.2.ρ → InInd π (ρ :: S)

def tameRep (χ : (ZMod g)ˣ →* ℂˣ) : GLRep g := ⟨1, Rep.of (Model.detRep 1 (Model.tame χ))⟩

def SuppAdds (σ π : GLRep g) (t : ℕ) {s : ℕ} (χ : Fin s → (ZMod g)ˣ →* ℂˣ) : Prop :=
  ∃ S S' : List (GLRep g), InInd π S ∧ InInd σ S' ∧
    S.Perm (S' ++ (List.ofFn fun i => List.replicate t (tameRep (χ i))).flatten)

def chainVecs {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (r t : ℕ) {s : ℕ} (χ : Fin s → (ZMod g)ˣ →* ℂˣ) : Submodule ℂ V where
  carrier := {v | ∀ (h : GL (Fin n) ℤ_[g]) (y : Fin s → Gn g t), tl r (red g n h : Mt g n) = 1 →
    (∀ i : Fin s, InPar (r + i * t) (red g n h : Mt g n)) →
    (∀ i : Fin s, br (r + i * t) t (red g n h : Mt g n) = (y i : Mt g t)) →
    π (inc g n h) v = ((∏ i, χ i (Matrix.GeneralLinearGroup.det (y i)) : ℂˣ) : ℂ) • v}
  add_mem' := fun {a b} ha hb h y h1 h2 h3 => by rw [map_add, ha h y h1 h2 h3, hb h y h1 h2 h3, smul_add]
  zero_mem' := fun h y _ _ _ => by rw [map_zero, smul_zero]
  smul_mem' := fun c v hv h y h1 h2 h3 => by rw [map_smul, hv h y h1 h2 h3, smul_comm]

theorem InInd.irr {π : GLRep g} {S : List (GLRep g)} (h : InInd π S) : IsIrrRep π.2.ρ := by
  cases h <;> assumption

end GlobalTheory.GLp.Supp
