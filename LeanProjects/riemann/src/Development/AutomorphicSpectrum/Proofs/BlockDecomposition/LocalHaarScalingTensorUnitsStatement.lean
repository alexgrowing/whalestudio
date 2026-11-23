import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingTensorUnits
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_scaling_tensor_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ (y : (R ⊗[F] E)ˣ) (n : Rˣ) (c : ℝ≥0), (n : R) ⊗ₜ[F] (1 : E) = sigR R σ y * y → lam.map (fun t => (n : R) * t) = c • lam → (coordW R b lam 1 1).map (fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => (y : R ⊗[F] E) * X a i) = c • coordW R b lam 1 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale.map_coordW_unit | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale.map_coordW_unit | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitScale.map_coordW_unit <;> assumption)
