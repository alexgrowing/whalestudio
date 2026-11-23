import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CharacterRegularityFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleAdmissibleFiniteLengthStatement

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.RealInd
open GlobalTheory.Dec (IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep IsUnitEquiv IsCharFn IsRegSS)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.LowestKTypeDetermines

namespace GlobalTheory.DSCharLowest

theorem isDS_of_cone {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (h : IsSqIntIrr ε σ)
    (h1 : ∃ S : Submodule ℂ V, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S)
    (h2 : ∀ (ν : Fin n → ℝ) (S : Submodule ℂ V), IsKTypeOf ε σ ν S → ∃ c : Fin n → Fin n → ℕ,
      (∀ a b, c a b ≠ 0 → a < b) ∧ ν = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) :
    IsDS ε lam σ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨c1, c2, c3, c4, c5, h1, fun μ S hS => ?_⟩
  obtain ⟨c, hc, rfl⟩ := h2 μ S hS
  unfold vNormSq
  rw [add_right_comm, lowK_add]
  have := nsq_add_cone (strictAnti_add_rho hl.1).antitone hc
  linarith [nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)]

theorem discreteSeriesCharacter_of_parameter : GlobalTheory.Published.IrreducibleUnitaryAdmissible →
    GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.CharacterRegularityFiniteLength →
    GlobalTheory.Published.DiscreteSeriesCharacterOfParameter → GlobalTheory.Dec.DSUnique → GlobalTheory.Published.DiscreteSeriesCharacter := by
  intro hadm han hreg hpar huniq n ε μ _ V _ _ _ lam σ hl hσ hU
  have hA : IsAdmRep ε σ := GlobalTheory.T.admissible_unitary_K_finite.1 hadm n ε V σ hU hσ.2.2.2.1
  have hF := (GlobalTheory.T.irreducible_admissible_finite_length han n ε V σ ⟨hσ.2.1, hA, hσ.2.2.2.1⟩).2
  obtain ⟨Θ, hΘ⟩ := hreg n ε μ V σ hA hF
  obtain ⟨V₀, _, _, _, σ₀, h₀, h1, h2, Θ₀, hΘ₀, hval⟩ := hpar n ε μ lam hl
  obtain ⟨T, hT⟩ := huniq n ε lam V₀ σ₀ V σ hl (isDS_of_cone hl h₀ h1 h2) hσ
  have he : IsUnitEquiv (ujRep h₀.2.2.1) (ujRep hU) := ⟨T, fun g v => hT _ g.2 v⟩
  refine ⟨Θ, hΘ, fun θ hθ => ?_⟩
  rw [← hval θ hθ]
  exact IsCharFn.unique isInducing_matCoord hΘ.1 (hΘ₀.of_isUnitEquiv he) hθ

end GlobalTheory.DSCharLowest
