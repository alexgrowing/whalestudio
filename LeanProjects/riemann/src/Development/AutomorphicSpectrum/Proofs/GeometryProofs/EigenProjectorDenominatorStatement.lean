import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorDenominator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
open NumberField GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_projector_denominator : ∀ (E : Type) [Field E] [NumberField E], ∃ D : ℕ, 0 < D ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω), ∃ T ∈ Sandwich.opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform | exact GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform | (intros; apply GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform <;> assumption)
