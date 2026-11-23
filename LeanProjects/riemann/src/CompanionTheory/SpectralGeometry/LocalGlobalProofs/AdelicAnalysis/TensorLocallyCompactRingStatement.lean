import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_locally_compact_ring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalRing (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ Continuous (sigR R σ) ∧ Continuous (Algebra.trace R (R ⊗[F] E)) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k) ∧ (∀ n M : ℕ, BorelSpace (Fin n → Fin M → R ⊗[F] E)) ∧ (∀ n : ℕ, IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E)))) ∧ (∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.TopK.topTens_props | exact GlobalTheory.CompanionTheory.SW.TopK.topTens_props | (intros; apply GlobalTheory.CompanionTheory.SW.TopK.topTens_props <;> assumption)
