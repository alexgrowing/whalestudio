import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicUnitaryStabilizerCocompact
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_unitary_stabilizer_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ C : Set (HA (AF F) σ (hypJ J)), IsCompact C ∧ ∀ h : HA (AF F) σ (hypJ J), ∃ c ∈ C, ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ (h * c⁻¹) (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Iwa.iwasawa | exact GlobalTheory.CompanionTheory.SW.Iwa.iwasawa | (intros; apply GlobalTheory.CompanionTheory.SW.Iwa.iwasawa <;> assumption)
