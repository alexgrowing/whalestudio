import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeKernelAddImage
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_le_kernel_add_image : ∀ (K : Type) [Field K] [NumberField K] (m m' : ℕ) (h : HermFam K (Fin m → K)) (h' : HermFam K (Fin m' → K)) (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (C : ℝ), 0 < C → ∀ W : Submodule (𝓞 K) (Fin m → K), W.FG → (∀ (σ : K →+* ℂ) (n : ℕ) (v : Fin n → Fin m → K), (∀ i, v i ∈ W) → ((C : ℂ) • h.gram σ v - h'.gram σ (q ∘ v)).PosSemidef) → deg h W ≤ deg h (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) + deg h' (W.map (q.restrictScalars (𝓞 K))) + (latRank K (W.map (q.restrictScalars (𝓞 K))) : ℝ) / 2 * Real.log C := by
  first | exact @GlobalTheory.deg_le_deg_ker_add_deg_map_add | exact GlobalTheory.deg_le_deg_ker_add_deg_map_add | (intros; apply GlobalTheory.deg_le_deg_ker_add_deg_map_add <;> assumption)
