import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec Matrix GlobalTheory.RealBessel

namespace UpperTheory.Lit.Bur

def IsGapDS {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : ℝ) : Prop :=
  ∃ (ε : Fin n → Bool) (lam : Fin n → ℝ) (fr : Matrix (Fin n) (Fin n) ℂ), IsUnit fr ∧
    frᴴ * Formalism.REAL.Jm ε * fr = J ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧
    Formalism.MainNotions.S.IsDS ε lam (fun g => σ (fr⁻¹ * g * fr))

def IsCompactCfg {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (z : Fin n → ℂ) : Prop :=
  1 ≤ m ∧
    (((Formalism.QuantumDeterminants.herm J z z).re < 0 ∧ ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) ∨
      (0 < (Formalism.QuantumDeterminants.herm J z z).re ∧ ∀ x : Fin m → ℂ, x ≠ 0 → (Formalism.QuantumDeterminants.herm J₀ x x).re < 0))

def BurGap : Prop :=
  ∀ (n m r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ), IsFrame J J₀ F e z → IsCompactCfg J J₀ z →
    ∀ χ : Matrix (Fin n) (Fin n) ℂ → ℂ, IsGeneric J e z χ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UH J) σ →
      IsIrredOn (UH J) σ → ∀ h : ℝ, 120 * (n : ℝ) ^ 3 ≤ h → IsGapDS J σ h →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W), IsContIrred (UH J₀) π₀ →
      Module.rank ℂ (besselForms J J₀ F e χ σ π₀ (smSub J σ)) ≤ 1

def BurGapPos : Prop :=
  ∀ (n m r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ), IsFrame J J₀ F e z → 1 ≤ m → (Formalism.QuantumDeterminants.herm J z z).re < 0 →
    (∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) →
    ∀ χ : Matrix (Fin n) (Fin n) ℂ → ℂ, IsGeneric J e z χ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UH J) σ →
      IsIrredOn (UH J) σ → ∀ h : ℝ, 120 * (n : ℝ) ^ 3 ≤ h → IsGapDS J σ h →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W), IsContIrred (UH J₀) π₀ →
      Module.rank ℂ (besselForms J J₀ F e χ σ π₀ (smSub J σ)) ≤ 1

end UpperTheory.Lit.Bur
