import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFibreMeasureLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMeasureByInvariantSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationHaarBaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_fibre_measure_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ 1)) (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J 1 μ ν m → ∀ X : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → gramR R σ J X = 0 → ∀ S : HermR R σ 1, m S ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeFibPos.fibre_ne_zero <;> assumption)
