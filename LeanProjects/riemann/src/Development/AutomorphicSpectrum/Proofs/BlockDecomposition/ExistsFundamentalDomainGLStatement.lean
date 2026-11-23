import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamental_domain_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (φ : GA E N → ℂ), IsSqInt φ →
  ∃ F : Set (GA E N), IsFundamentalDomain (latticeGL E N) F μ := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt | exact GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt | (intros; apply GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt <;> assumption)
