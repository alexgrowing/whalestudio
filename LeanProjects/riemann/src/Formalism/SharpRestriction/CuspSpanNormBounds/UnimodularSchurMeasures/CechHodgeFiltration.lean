import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Obj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def ff_psi (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (X : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℂ) • ∫ kk, d30f ε lam σ w X kk ∂(Formalism.REAL.muK ε)

def ff_IsPsi (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ k X, k ∈ Formalism.REAL.Kset ε → Formalism.REAL.inP ε X → Ψ (k * NormedSpace.exp X) = σ k ∘L ff_psi ε lam σ w X

def ff_Data (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H)
    (h : ℝ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam lam ∧ IsDS ε lam σ ∧ IsOrthProjOnto E (lowKSub ε lam σ) ∧ IsHighestUnit ε lam σ w ∧
    Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h

def ff_Sph (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ k₁ ∈ Formalism.REAL.Kset ε, ∀ k₂ ∈ Formalism.REAL.Kset ε, ∀ g ∈ UJset ε, Ψ (k₁ * g * k₂) = σ k₁ ∘L Ψ g ∘L σ k₂

def ff_Compr (ε : Fin n → Bool) (E : H →L[ℂ] H) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ g ∈ UJset ε, E ∘L Ψ g ∘L E = Ψ g

def ff_Eig (ε : Fin n → Bool) (c : ℕ → ℂ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪x, Ψ g y⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g

def ff_DSSum (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ (N : ℕ) (φ : Fin N → Formalism.REAL.UJ ε → ℂ), (∀ i, IsDSCoef ε (φ i)) ∧
    ∀ g : Formalism.REAL.UJ ε, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i, φ i g

end Obj

def FResId : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ff_psi ε lam σ w 0 = E

def FSph : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ff_Sph ε σ Ψ

def FCompr : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ff_Compr ε E Ψ

def FPsiEig (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ff_Eig ε (χ n lam) Ψ

def FKFin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    FiniteDimensional ℂ (lowKSub ε lam σ) →
    ∀ Ψ, ff_Sph ε σ Ψ → ff_Compr ε E Ψ → ∀ x y : H, IsKFinFunOn ε (fun g => ⟪x, Ψ g y⟫_ℂ)

def FDecay : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    ff_psi ε lam σ w 0 = E → ∀ X, Formalism.REAL.inP ε X →
    ‖ff_psi ε lam σ w X‖ ≤ decBound (min (pOf ε) (qOf ε)) h X

def MatrixCoeffSquareIntegrable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H) (w : H) (h : ℝ), ff_Data ε lam σ E w h →
    (∀ X, Formalism.REAL.inP ε X → ‖ff_psi ε lam σ w X‖ ≤ decBound (min (pOf ε) (qOf ε)) h X) →
    ∀ Ψ, ff_IsPsi ε lam σ w Ψ → ∀ x y : H, Continuous (fun g : Formalism.REAL.UJ ε => ⟪x, Ψ (umat g) y⟫_ℂ) →
    MemLp (fun g : Formalism.REAL.UJ ε => ⟪x, Ψ (umat g) y⟫_ℂ) 2 (Formalism.REAL.muG ε)

def FSphUnique (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : H →L[ℂ] H), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    IsOrthProjOnto E (lowKSub ε lam σ) →
    ∀ Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H), ff_Sph ε σ Ψ → ff_Compr ε E Ψ → Ψ 1 = E → ff_Eig ε (χ n lam) Ψ →
      ff_DSSum ε Ψ → ∀ g ∈ UJset ε, Ψ g = E ∘L σ g ∘L E

end Formalism.MainNotions.LeviCoordinates

end
