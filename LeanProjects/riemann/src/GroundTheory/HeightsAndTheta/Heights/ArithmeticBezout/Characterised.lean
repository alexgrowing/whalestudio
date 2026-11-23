import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ConeIntegralMass.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      coneIntegral h W e (fun _ => 1) = δ

def ChowFormBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I k f →
      (∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, IsProjPrime W) ∧
        IsChowFormCycle (fundCycle (I.map (MvPolynomial.map σ))) k (MvPolynomial.map σ f)

def ChowHeightCharacterised.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (H : ArchData K n)
    (J : Ideal (MvPolynomial (Fin n) K) → ℝ),
    (∀ (e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K)
        (u : Fin n → 𝓞 K),
      IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f →
      linForm (fun j => (u j : K)) ∉ I →
        J I = (∑ W ∈ (divCycle I fun j => (u j : K)).support,
                ((divCycle I fun j => (u j : K)) W : ℝ) * J W) +
          (1 / Module.finrank ℚ K : ℝ) *
            (vertTerm I (e + 1) u -
              ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
                (fsLog (H.normAt σ) fun j => σ (u j)))) →
    ∀ (e δ : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K),
      IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f → J I = chowHt H (e + 1) δ f

theorem ConeIntegralMass.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℂ) :=
  ⟨isProjPrime_point ℂ, isChowForm_point ℂ, isMultiHomog_point ℂ⟩

theorem ChowFormBaseChange.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 (X (0, 0)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ⟩

end

end GroundTheory.Heights₂.Heights
