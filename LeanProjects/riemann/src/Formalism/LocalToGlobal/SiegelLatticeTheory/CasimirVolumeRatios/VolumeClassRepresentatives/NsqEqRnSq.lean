import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.SobTEqSobTM
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CasScalar
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.GenApplyZero

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace Formalism.L2.S.S7.CasimirNormBounds

open Formalism.MainNotions.S Formalism.REAL Formalism.L2.SG.Pf.admitted

variable {n : ℕ}

def rn (u : Fin n → ℝ) : ℝ := Real.sqrt (nsq u)

def cK (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := nsq (μ + rhoC ε) - nsq (rhoC ε)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def OmKg (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a : H) : H :=
  -∑ p : Fin n × Fin n, if ε p.1 = ε p.2 then
    ((wt p : ℝ) : ℂ) • dS σ (gen ε p) (dS σ (gen ε p) a) else 0

def WK (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (r : ℝ) : Submodule ℂ H :=
  sSup {S | ∃ μ, IsKTypeOf ε σ μ S ∧ rn (μ - Λ) ≤ r}

end Formalism.L2.S.S7.CasimirNormBounds

namespace Formalism.L2.S.S7.CasimirNormBounds

open Formalism.MainNotions.S Formalism.REAL Formalism.L2.SG.Pf.admitted

def KCasValue : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
      (∀ p : Fin n × Fin n, ε p.1 = ε p.2 → ∀ a ∈ S,
        HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • gen ε p)) a) (dS σ (gen ε p) a) 0 ∧
          dS σ (gen ε p) a ∈ S) ∧
      ∀ a ∈ S, OmKg ε σ a = ((cK ε μ : ℝ) : ℂ) • a

def KTypeShift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ →
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∀ a ∈ S, ∀ E : Matrix (Fin n) (Fin n) ℂ, inG ε E →
      ∃ a' : H, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • E)) a) a' 0 ∧
        a' ∈ sSup {S' : Submodule ℂ H | ∃ μ', IsKTypeOf ε σ μ' S' ∧ nsq (μ' - μ) ≤ 2}

end Formalism.L2.S.S7.CasimirNormBounds
