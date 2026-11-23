import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximation
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typed_space_approximation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (R ε δ : ℝ) (α : GA E N → ℂ) (F : Set (GA E N)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → 0 < ε →
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ →
  ∃ Ω : Set (GA E N), IsCompact Ω ∧ ∀ (V : Submodule ℂ (Sm E N)) (ψ : Sm E N), IsDiscrete V → ψ ∈ V → TypeB K W ψ →
    InfBdd R V → (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) →
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) →
    (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 → 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ.1 x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Conc.conc | exact GlobalTheory.CompanionTheory.Conc.conc | (intros; apply GlobalTheory.CompanionTheory.Conc.conc <;> assumption)
