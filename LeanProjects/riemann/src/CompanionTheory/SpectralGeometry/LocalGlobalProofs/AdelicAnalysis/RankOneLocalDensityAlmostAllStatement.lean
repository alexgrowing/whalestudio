import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAll
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_local_density_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 → |(m (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocGood.density_standard_lattice | exact GlobalTheory.CompanionTheory.SW.LocGood.density_standard_lattice | (intros; apply GlobalTheory.CompanionTheory.SW.LocGood.density_standard_lattice <;> assumption)
