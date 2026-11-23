import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def IntE (x : E) : Prop := ∃ o : 𝓞 E, (o : E) = x

def StSet (W : Matrix (Fin n) (Fin n) E) : Set (Matrix.GeneralLinearGroup (Fin n) E) :=
  {a | Formalism.MainNotions.S.IsLoUni (a : Matrix (Fin n) (Fin n) E) ∧ ∃ b : Matrix (Fin n) (Fin n) E,
    Formalism.MainNotions.S.IsUpUni b ∧ (a : Matrix (Fin n) (Fin n) E) * W * b = W}

def BddDen (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) E)) : Prop :=
  ∃ N : ℕ, N ≠ 0 ∧ ∀ h ∈ H, ∀ i j, IntE ((N : E) * (h : Matrix (Fin n) (Fin n) E) i j)

def CongIn (W : Matrix (Fin n) (Fin n) E) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) E)) : Prop :=
  ∃ N : ℕ, N ≠ 0 ∧ ∀ a : Matrix.GeneralLinearGroup (Fin n) E, a ∈ StSet W →
    (∀ i j, IntE (((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) / (N : E))) → a ∈ H

def StClosed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : Matrix (Fin n) (Fin n) E),
    (1 : Matrix.GeneralLinearGroup (Fin n) E) ∈ StSet W ∧
    (∀ a ∈ StSet W, ∀ b ∈ StSet W, a * b ∈ StSet W) ∧ (∀ a ∈ StSet W, a⁻¹ ∈ StSet W)

def Commens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : Matrix (Fin n) (Fin n) E)
    (H K : Subgroup (Matrix.GeneralLinearGroup (Fin n) E)),
    (H : Set (Matrix.GeneralLinearGroup (Fin n) E)) ⊆ StSet W → BddDen H → CongIn W K → K.relIndex H ≠ 0

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
