import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocallyFinite
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_pure_tensor_eq_prod_of_isEulerProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → IsLocallyFiniteMeasure minf → (∀ v, IsLocallyFiniteMeasure (m v)) → ∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf → Measurable Φ ∧ Integrable Φ I ∧ Multipliable (fun v => ∫ X, Φv v X ∂(m v)) ∧ ∫ X, Φ X ∂I = (∫ X, Φinf X ∂minf) * ∏' v, ∫ X, Φv v X ∂(m v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerInt.euler_int | exact GlobalTheory.CompanionTheory.SW.EulerInt.euler_int | (intros; apply GlobalTheory.CompanionTheory.SW.EulerInt.euler_int <;> assumption)
