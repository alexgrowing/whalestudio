import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open Matrix Finset

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

open Formalism.MainNotions.S

section Defs

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def orbit (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : ℝ → H :=
  fun t => σ (NormedSpace.exp ((t : ℂ) • X)) v

def dAct (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (orbit σ X v) 0

def IsDiffVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∀ X, Formalism.REAL.inG ε X → DifferentiableAt ℝ (orbit σ X v) 0

def dWord (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (l : List (Matrix (Fin n) (Fin n) ℂ)) (v : H) : H :=
  l.foldr (dAct σ) v

def stepSpace (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : ℕ) :
    Submodule ℂ H :=
  Submodule.span ℂ {v | ∃ (l : List (Matrix (Fin n) (Fin n) ℂ)) (u : H), l.length ≤ P ∧
    (∀ X ∈ l, Formalism.REAL.inG ε X) ∧ u ∈ lowKSub ε lam σ ∧ v = dWord σ l u}

def IsONFamily (ε : Fin n → Bool) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, Formalism.REAL.inG ε (E i)) ∧ ∀ i j, (Matrix.trace (E i * (E j)ᴴ)).re = if i = j then 1 else 0

def stepConst (n : ℕ) (b : ℝ) (P : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 + 3 / 2 * (n : ℝ) ^ (3 / 2 : ℝ) + 3 * (P : ℝ)

theorem stepSpace_zero (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    stepSpace ε lam σ 0 = lowKSub ε lam σ := by
  have : {v | ∃ (l : List (Matrix (Fin n) (Fin n) ℂ)) (u : H), l.length ≤ 0 ∧
      (∀ X ∈ l, Formalism.REAL.inG ε X) ∧ u ∈ lowKSub ε lam σ ∧ v = dWord σ l u} = (lowKSub ε lam σ : Set H) := by
    ext v
    constructor
    · rintro ⟨l, u, hl, -, hu, rfl⟩
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      subst this
      exact hu
    · intro hv
      exact ⟨[], v, le_rfl, by simp, hv, rfl⟩
  rw [stepSpace, this, Submodule.span_eq]

theorem stepSpace_mono (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Monotone (stepSpace ε lam σ) := by
  intro P Q h
  refine Submodule.span_mono ?_
  rintro v ⟨l, u, hl, h1, h2, h3⟩
  exact ⟨l, u, hl.trans h, h1, h2, h3⟩

end Defs

example (ε : Fin 1 → Bool) : IsONFamily ε (fun _ => Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  refine ⟨fun _ => ?_, fun i j => ?_⟩
  · simp [Formalism.REAL.inG, Matrix.conjTranspose_smul]
  · have : i = j := Subsingleton.elim (α := Fin 1) i j
    simp [this, Matrix.conjTranspose_smul, smul_smul]

def StepBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (b : ℝ) (P : ℕ),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → (∀ a, |lam a| ≤ b ^ 2) →
      FiniteDimensional ℂ (stepSpace ε lam σ P) ∧
      (∀ w ∈ stepSpace ε lam σ P, IsDiffVec ε σ w) ∧
      (∀ E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, IsONFamily ε E → ∀ w ∈ stepSpace ε lam σ P,
        ∑ i, ‖dAct σ (E i) w‖ ^ 2 ≤ stepConst n b P ^ 2 * ‖w‖ ^ 2) ∧
      ∀ E, Formalism.REAL.inG ε E → ∀ w ∈ stepSpace ε lam σ P,
        ‖dAct σ E w‖ ≤ Real.sqrt (Formalism.REAL.hs E) * stepConst n b P * ‖w‖

end GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace
