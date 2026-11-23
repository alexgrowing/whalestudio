import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayLimit
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingByUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteAdeleHaarScalingTotallyRealStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarScalingTensorUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticePreservedCofinitelyByUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLatticeMeasureEqOneStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_theta_integral_ray_limit : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → (∀ᶠ ε : ℝ in 𝓝[>] 0, Th φ A (y * ofF (r ε)) ≠ ⊤) → Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (y * ofF (r ε))) (𝓝[>] 0) (𝓝 ((ENNReal.ofReal (md n))⁻¹ * vol b li lam S φ A)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit.equi_unit | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit.equi_unit | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit.equi_unit <;> assumption)
