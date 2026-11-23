import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CharacterRegularityFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspidalOrbitalIntegrals
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleAdmissibleFiniteLengthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TemperedKFiniteCoefficientsStatement

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.Published

theorem pseudoCoefficientUpq_of_hypotheses (hUA : IrreducibleUnitaryAdmissible) (hKA : KFiniteCoefficientsAnalytic)
    (hCR : CharacterRegularityFiniteLength) (hPE : PseudoCoefficientExistence) (hCO : CuspidalOrbitalIntegrals) :
    PseudoCoefficientUpq := by
  intro n ε X _ _ σ h μ _
  haveI := h.1
  obtain ⟨f, hf, hbi, hpt⟩ := hPE n ε X σ h μ
  have hadm : IsAdmRep ε σ := (GlobalTheory.T.admissible_unitary_K_finite.1 hUA) n ε X σ h.2.2.1 h.2.2.2.1
  have hfl : HasFiniteLength ε σ := (GlobalTheory.T.irreducible_admissible_finite_length hKA n ε X σ ⟨h.2.1, hadm, h.2.2.2.1⟩).2
  obtain ⟨Θ, hΘ⟩ := hCR n ε μ X σ hadm hfl
  have hch : IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ := hΘ.1
  refine ⟨f, hbi, ⟨hf, hpt.1, ?_, ?_, ⟨Θ, hch, ?_⟩⟩⟩
  · intro U _ _ _ π hu hi ht hne
    exact hpt.2 U π hu hi (GlobalTheory.T.tempered_K_finite_coefficients hUA n ε μ U π hu hi ht) hne
  · intro s hs hnc dt _ _
    exact (hCO n ε X σ h μ f hf hbi hpt Θ hch s hs dt).2 hnc
  · intro s hs hc dt _ _
    exact (hCO n ε X σ h μ f hf hbi hpt Θ hch s hs dt).1 hc

end GlobalTheory.Published

end
