import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeBadPrimesIffGramDet
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalHermitianLattice_badPrimes_iff_gramDet : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → ∀ (j : ℕ) (b : Module.Basis (Fin j) K V) (P : Ideal (𝓞 K)), P.IsMaximal → (P ∈ badP h M ↔ conjIdeal (K := K) P = P ∧ ¬ ∃ c : K, c ≠ 0 ∧ star c * c * (Matrix.of fun i l => h (b i) (b l)).det ∈ locR (K := K) P ∧ (star c * c * (Matrix.of fun i l => h (b i) (b l)).det)⁻¹ ∈ locR (K := K) P) := by
  first | exact @GlobalTheory.MaxLatDet.main | exact GlobalTheory.MaxLatDet.main | (intros; apply GlobalTheory.MaxLatDet.main <;> assumption)
