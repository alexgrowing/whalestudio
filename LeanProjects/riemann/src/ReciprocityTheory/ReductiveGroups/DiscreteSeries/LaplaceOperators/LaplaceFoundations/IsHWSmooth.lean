import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dNode (k r : ℕ) : Fin (2 * r + k + 1) → ℝ :=
  fun a => if a.val < k then 0 else -((a.val + 1 - k : ℕ) : ℝ)

def dMat (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => ((d a : ℝ) : ℂ)

def stJ (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Jm ε * Xᴴ * Jm ε

def InLL (ε : Fin n → Bool) (d : Fin n → ℝ) (a b : Fin n) : Prop := ε a = ε b ∧ d a = d b

def InNP (ε : Fin n → Bool) (d : Fin n → ℝ) (a b : Fin n) : Prop :=
  (a < b ∧ ε a = ε b ∧ d a ≠ d b) ∨ (b < a ∧ ε a ≠ ε b)

def InNM (ε : Fin n → Bool) (d : Fin n → ℝ) (a b : Fin n) : Prop := InNP ε d b a

open Classical in

def partNM (ε : Fin n → Bool) (d : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if InNM ε d a b then X a b else 0

def qForm (ε : Fin n → Bool) (d : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  -(trace (dMat d * (Y * partNM ε d Y - partNM ε d Y * Y)))

def l1 (X : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖

section Datum

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def IsHWDatum (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (w : M) : Prop :=
  IsGlRep E ∧ IsInfUnitary ε E ∧ ‖w‖ = 1 ∧ IsKHWVec ε E (lowK ε lam) w ∧
    casimir E w = ((casVal lam : ℝ) : ℂ) • w

end Datum

section Smooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsHWSmooth (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ)
    (w : H) : Prop :=
  IsURepOn (UJset ε) σ ∧ ∃ hw : w ∈ smD ε σ, ‖w‖ = 1 ∧
    IsKHWVec ε (smE ε σ) (lowK ε lam) (⟨w, hw⟩ : smD ε σ) ∧
    casimir (smE ε σ) (⟨w, hw⟩ : smD ε σ) = ((casVal lam : ℝ) : ℂ) • (⟨w, hw⟩ : smD ε σ)

open Classical in

def phiW (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (X : Matrix (Fin n) (Fin n) ℂ) : H :=
  if hw : w ∈ smD ε σ then ((actM (smE ε σ) X (⟨w, hw⟩ : smD ε σ) : smD ε σ) : H) else 0

end Smooth

def z0 (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))

def cBase (r : ℕ) (t : ℝ) : Fin r → ℂ := fun _ => -2 * Complex.I * (t : ℂ)

def WCols (k r : ℕ) (P : Mat k r) : Prop :=
  ∀ j : Fin k, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r j.castSucc) =
    Formalism.QuantumDeterminants.bvec (⟨j.val, by omega⟩ : Fin (2 * r + k + 1))

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
