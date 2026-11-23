import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InfinitesimalEquivalenceUnitaryGroupPQ
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.GKLie GlobalTheory.CompanionTheory.GKClosure
open GlobalTheory.SmoothGlob (lieSet)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def actV [CompleteSpace H] (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (kFinVec ε σ) :=
  vAct hU.1 (isGKSub_kFinVec hU hI)

def posProj (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else 0

def degOf (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := ∑ a, if ε a then μ a else 0

variable [CompleteSpace H] (hU : IsURepOn (UJset ε) σ) (hI : IsIrredOn (UJset ε) σ)

end GlobalTheory.CompanionTheory.Hypotheses₂

namespace GlobalTheory.CompanionTheory.Hypotheses₂

section Words

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def wordE (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (l : List (Matrix (Fin n) (Fin n) ℂ)) : Module.End ℂ M :=
  (l.map A).prod

def wordSpan (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (P : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (T : Submodule ℂ M) : Submodule ℂ M :=
  Submodule.span ℂ {w | ∃ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ P) ∧ ∃ t ∈ T, w = wordE A l t}

@[simp] theorem wordE_nil (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) : wordE A [] = 1 := rfl

@[simp] theorem wordE_cons (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (Z : Matrix (Fin n) (Fin n) ℂ)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : wordE A (Z :: l) = A Z * wordE A l := by
  simp [wordE]

end Words

section Parts

variable {n : ℕ}

def pPlusS (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := GlobalTheory.HolDS.pPlus ε
  add_mem' := fun {x y} hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

def pMinusS (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := GlobalTheory.HolDS.pMinus ε
  add_mem' := fun {x y} hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

def kS (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | Y * Jm ε = Jm ε * Y}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.smul_mul, Matrix.mul_smul, hx]

def upperC (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | ∀ a b, ¬ (a ≤ b ∧ ε a = ε b) → Y a b = 0}
  add_mem' := fun {x y} hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

def lowerC (ε : Fin n → Bool) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | ∀ a b, ¬ (b < a ∧ ε a = ε b) → Y a b = 0}
  add_mem' := fun {x y} hx hy a b h => by simp [hx a b h, hy a b h]
  zero_mem' := fun a b _ => rfl
  smul_mem' := fun c x hx a b h => by simp [hx a b h]

end Parts

end GlobalTheory.CompanionTheory.Hypotheses₂

end
