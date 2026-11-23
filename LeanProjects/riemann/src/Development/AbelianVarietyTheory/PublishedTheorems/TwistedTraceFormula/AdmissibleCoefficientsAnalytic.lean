import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.Published

def AdmissibleCoefficientsAnalytic : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π →
    ∀ v w : H, IsKFin ε π v → IsKFin ε π w → AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ

def LeviSubmoduleDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ S : Submodule ℂ V, S ≠ ⊥ → (∀ v ∈ S, IsKFinIn (leviOne ε W) σ v) →
        (∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
          ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) v' 0) →
        Dense (S : Set V)

def HarishChandraAnalyticity : Prop := AdmissibleCoefficientsAnalytic ∧ LeviSubmoduleDense

example {n : ℕ} (ε : Fin n → Bool) : IsAdmRep ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧
    ∀ v, IsKFin ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) v :=
  ⟨(isIrrAdm_det (ε := ε)).2.1, (det_isURepOn ε).2.2⟩

end GlobalTheory.Published

end
