import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternal
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_decomposition_internal : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | exact GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.isInternal_eigSp <;> assumption)
