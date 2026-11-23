import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFibreMeasureLocal
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fibre_measure_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : GL (Fin M) (R ⊗[F] E)) (l : R), IsUnit l → cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) l) • JR R J → ∀ a c : ℝ≥0, μ.map (actTup R g) = a • μ → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = c • ν → ∀ S, (m S).map (actTup R g) = (a / c) • m (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude | exact GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude | (intros; apply GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude <;> assumption)
