import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicPrimitiveVectorCompactRescale
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_primitive_vector_compact_rescale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), ∃ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ z : Fin M → AF F ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (AF F ⊗[F] E)ˣ) (z : Fin 1 → Fin M → AF F ⊗[F] E), (a : AF F ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : AF F ⊗[F] E) • y) 0 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PrimA.unimodular_compact_mod_units | exact GlobalTheory.CompanionTheory.SW.PrimA.unimodular_compact_mod_units | (intros; apply GlobalTheory.CompanionTheory.SW.PrimA.unimodular_compact_mod_units <;> assumption)
