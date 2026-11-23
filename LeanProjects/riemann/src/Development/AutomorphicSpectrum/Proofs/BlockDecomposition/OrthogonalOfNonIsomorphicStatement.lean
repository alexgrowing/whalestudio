import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_of_non_isomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ x in F, φ.1 x * (starRingEnd ℂ) (ψ.1 x) ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV | exact GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV | (intros; apply GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV <;> assumption)
