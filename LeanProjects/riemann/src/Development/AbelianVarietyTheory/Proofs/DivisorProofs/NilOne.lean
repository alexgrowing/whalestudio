import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenSubHwOfSurjective

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.OneParam GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.RealK

namespace GlobalTheory.ThK.StepK

def lowIx {R S : ℕ} : Ix (R + 1) (S + 1) → Option (Ix R S)
  | .inl i => Fin.cases (motive := fun _ => Option (Ix R S)) none (fun i => some (.inl i)) i
  | .inr j => Fin.cases (motive := fun _ => Option (Ix R S)) none (fun j => some (.inr j)) j

def embL {R S : ℕ} (X : Mat R S) : Mat (R + 1) (S + 1) :=
  Matrix.of fun a b => match lowIx a, lowIx b with
    | some a', some b' => X a' b'
    | _, _ => 0

def vZero (R S : ℕ) : Ix (R + 1) (S + 1) → ℂ := Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1

def nilOne (R S : ℕ) : Set (Mat (R + 1) (S + 1)) :=
  {Z | Z *ᵥ vZero R S = 0 ∧ (∀ u, u ⬝ᵥ (Jm (R + 1) (S + 1) *ᵥ vZero R S) = 0 → ∃ c : ℂ, Z *ᵥ u = c • vZero R S) ∧
    ∀ u, (Z *ᵥ u) ⬝ᵥ (Jm (R + 1) (S + 1) *ᵥ vZero R S) = 0}

def dC (R S : ℕ) : Mat (R + 1) (S + 1) := Eab (.inl 0) (.inl 0) + Eab (.inr 0) (.inr 0)

def dS (R S : ℕ) : Mat (R + 1) (S + 1) := Eab (.inl 0) (.inr 0) + Eab (.inr 0) (.inl 0)

def twL (P Q R S : ℕ) (κ : ℤ) (m₀ : ℚ) : Ix R S → ℚ := fun c => lam P Q R S κ c + m₀

end GlobalTheory.ThK.StepK
