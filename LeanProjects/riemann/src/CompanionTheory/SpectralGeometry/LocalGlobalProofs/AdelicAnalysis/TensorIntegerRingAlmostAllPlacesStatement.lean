import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_integer_ring_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) ∧ (∀ y ∈ O, sigR (Fv F v) σ y ∈ O) ∧ Finite (MaximalSpectrum O) ∧ IsUnit (2 : O) ∧ (∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ) ∧ (∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O, (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧ ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1) ∧ ∀ β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ a : O, (a : Fv F v ⊗[F] E) * sigR (Fv F v) σ a = β := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodRing.good_ring | exact GlobalTheory.CompanionTheory.SW.GoodRing.good_ring | (intros; apply GlobalTheory.CompanionTheory.SW.GoodRing.good_ring <;> assumption)
