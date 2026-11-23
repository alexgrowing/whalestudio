import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Formalism.QuantumDeterminants

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

section Bessel

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

def chiInv (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (h m : Mat k r) (ξ : Vp) : Vp :=
  star (ψ m) • π h⁻¹ ξ

def sInt (μW μN : Measure (Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (f : Mat k r → ℂ) (ξ : Vp) (x : Mat k r) : Vp :=
  ∫ p : Mt k r × Mt k r, f (Matrix.of p.1 * Matrix.of p.2 * x) •
    chiInv ψ π (Matrix.of p.1) (Matrix.of p.2) ξ ∂(μW.prod μN)

def IsBData (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (μW μN : Measure (Mt k r)) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ (∀ a, c a ≠ 0) ∧ Formalism.MainNotions.S.IsHCTypeW k r z u π ∧
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW ∧ Formalism.MainNotions.S.IsHaarOn (Nset k r) μN

end Bessel

section Coef

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Λ : Fin (2 * r + k + 1) → ℝ}

def psiCoef (T : S7.KType ε Λ) (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r) (v₁ v₂ : T.V)
    (g : Mat k r) : ℂ :=
  ⟪v₂, S7.PsiM T μ (P * g * P⁻¹) v₁⟫_ℂ

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

def aaFun (T : S7.KType ε Λ) (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r)
    (μW μN : Measure (Mt k r)) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (v₁ v₂ : T.V) (ξ : Vp) (x₀ x : Mat k r) : Vp :=
  sInt μW μN ψ π (fun g => psiCoef T μ P v₁ v₂ (x₀⁻¹ * g)) ξ x

end Coef

section B

variable {k r : ℕ}

def BesselNZ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ) : Prop :=
  ∃ (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) (_ : NormedAddCommGroup Vp)
    (_ : InnerProductSpace ℂ Vp) (_ : CompleteSpace Vp) (π : Mat k r → (Vp →L[ℂ] Vp))
    (μW μN : Measure (Mt k r)),
    S7.IsMu lam μ ∧ Formalism.MainNotions.S.IsCayley k r ε P ∧ IsBData z c u π μW μN ∧
    ∃ (v₁ v₂ : T.V) (ξ : Vp) (x₀ x : Mat k r), x₀ ∈ UH (Hpk k r) ∧ x ∈ UH (Hpk k r) ∧
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x ≠ 0

def BesselAll (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (u : Fin k → ℝ) : Prop :=
  ∀ (T : S7.KType ε (lowK ε lam)) (μ : Fin (2 * r + k + 1) → ℤ) (P : Mat k r)
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Vp : Type) [NormedAddCommGroup Vp]
    [InnerProductSpace ℂ Vp] [CompleteSpace Vp] (π : Mat k r → (Vp →L[ℂ] Vp))
    (μW μN : Measure (Mt k r)),
    S7.IsMu lam μ → Formalism.MainNotions.S.IsCayley k r ε P → IsBData z c u π μW μN →
    ∀ v : T.V, v ≠ 0 → ∃ (ξ : Vp) (x₀ x : Mat k r), x₀ ∈ UH (Hpk k r) ∧ x ∈ UH (Hpk k r) ∧
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v v ξ x₀ x ≠ 0

end B

section Gap

variable {n : ℕ}

def hNeed (ε : Fin n → Bool) : ℝ :=
  max (2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)))
    (max (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2)
      (8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) *
        (4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) + 1)))

def GapLap (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) : Prop :=
  StrictAnti lam ∧ GapAtLeast ε lam h ∧ hNeed ε < h

end Gap

section L2

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

def equivariantL2Space (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp))
    (μG ν : Measure (Mt k r)) : Set (Mat k r → Vp) :=
  {W | AEStronglyMeasurable (fun x => W (Matrix.of x)) μG ∧ AEStronglyMeasurable (fun x => W (Matrix.of x)) ν ∧
    Formalism.MainNotions.S.IsSPsiEquiv z ψ π W ∧ Formalism.MainNotions.S.l2SG ν W < ⊤}

def rtr (g : Mat k r) (W : Mat k r → Vp) : Mat k r → Vp := fun x => W (x * g)

end L2

end ReciprocityTheory.ChartRestriction.DS.Lap
