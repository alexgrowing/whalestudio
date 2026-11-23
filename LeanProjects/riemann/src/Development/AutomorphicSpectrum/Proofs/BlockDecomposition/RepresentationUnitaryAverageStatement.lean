import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentationUnitaryAverage
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_unitary_average : ∀ {K M H X : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure] [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ K M) (ι : M →ₗ[ℂ] H) (U U' : Submodule ℂ M) (ev : X → M →ₗ[ℂ] ℂ),
  (∀ k, ∀ x ∈ U', ∀ y ∈ U, ⟪ι (ρ k x), ι (ρ k y)⟫_ℂ = ⟪ι x, ι y⟫_ℂ) →
  (∀ k, ∀ x ∈ U', ∀ y ∈ U', ⟪ι (ρ k x), ι (ρ k y)⟫_ℂ = ⟪ι x, ι y⟫_ℂ) →
  (∀ x ∈ U, ∃ A : Submodule ℂ M, FiniteDimensional ℂ A ∧ x ∈ A ∧ A ≤ U ∧ (∀ k, ∀ a ∈ A, ρ k a ∈ A) ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (ρ k a)) →
  (∀ x ∈ U', ∃ A : Submodule ℂ M, FiniteDimensional ℂ A ∧ x ∈ A ∧ A ≤ U' ∧ (∀ k, ∀ a ∈ A, ρ k a ∈ A) ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (ρ k a)) →
  (∀ W : Submodule ℂ (K → ℂ), FiniteDimensional ℂ W → FiniteDimensional ℂ (Submodule.span ℂ {x | x ∈ U' ∧ ∀ t, (fun k => ev t (ρ k x)) ∈ W})) →
  ∀ x ∈ U, ∃ y ∈ U', ∀ z ∈ U', ⟪ι z, ι x⟫_ℂ = ⟪ι z, ι y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector | exact GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector | (intros; apply GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector <;> assumption)
