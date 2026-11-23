import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CharacterRegularityFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeylIntegrationSum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InducedCharacterVanishing
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InducedAdmissibleFiniteLength
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleAdmissibleFiniteLengthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylGroupOrderNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCartanSystemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesCharacterFormulaStatement

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.HCChar

theorem characterRegularity_of_finiteLength (hA : KFiniteCoefficientsAnalytic)
    (hR : CharacterRegularityFiniteLength) : CharacterRegularity :=
  fun n ε μ _ V _ _ _ π h => hR n ε μ V π h.2.1 (GlobalTheory.T.irreducible_admissible_finite_length hA n ε V π h).2

theorem inducedCharacterSupport_of_vanishing (hR : CharacterRegularityFiniteLength)
    (hV : InducedCharacterVanishing) (hI : InducedAdmissibleFiniteLength) : InducedCharacterSupport := by
  intro n ε μ _ a j W hW hj _ V _ _ _ _ σ h1 h2 s X _ _ _ ρ ι hm h
  obtain ⟨hadm, hfl⟩ := hI n ε a j W hW hj V σ h1 h2 s X ρ ι hm
  obtain ⟨Θ, hΘ⟩ := hR n ε μ X ρ hadm hfl
  obtain ⟨Θ', h3, h4⟩ := hV n ε μ a j W hW hj V σ h1 h2 s X ρ ι hm h
  refine ⟨Θ, hΘ, fun g hg hx => ?_⟩
  rw [hΘ.1.unique isInducing_matCoord h3 hg, h4 g hg hx]

theorem harishChandraCharacters_of_clauses : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CharacterRegularityFiniteLength → GlobalTheory.Published.DiscreteSeriesCharacterOfParameter → GlobalTheory.Published.WeylIntegrationSum → GlobalTheory.Published.InducedCharacterVanishing → GlobalTheory.Published.InducedAdmissibleFiniteLength → GlobalTheory.Published.HarishChandraCharacters :=
  fun hU hA hC hR hD hW hV hI =>
    ⟨characterRegularity_of_finiteLength hA hR,
      GlobalTheory.T.discrete_series_character_formula hU hA hR hD (GlobalTheory.LowestKTypeDetermines.dsUnique_of_dsClass
        (GlobalTheory.Published.discreteSeriesClassification_iff.1 hC)),
      fun n ε => ⟨GlobalTheory.T.exists_cartan_system n ε, GlobalTheory.T.weyl_group_order_ne_zero n ε, fun μ _ => hW n ε μ⟩,
      inducedCharacterSupport_of_vanishing hR hV hI⟩

end GlobalTheory.HCChar

end
