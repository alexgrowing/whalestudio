import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDetGramAppendLe
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_gram_append_le : ∀ (K : Type) [Field K] [NumberField K] (m m' : ℕ) (h : HermFam K (Fin m → K)) (h' : HermFam K (Fin m' → K)) (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (C : ℝ), 0 < C → ∀ (σ : K →+* ℂ) (s t : ℕ) (a : Fin s → Fin m → K) (b : Fin t → Fin m → K), LinearIndependent K (Fin.append a b) → LinearIndependent K (q ∘ b) → (∀ i, q (a i) = 0) → ((C : ℂ) • h.gram σ (Fin.append a b) - h'.gram σ (q ∘ Fin.append a b)).PosSemidef → Real.log (h.gram σ a).det.re + Real.log (h'.gram σ (q ∘ b)).det.re ≤ Real.log (h.gram σ (Fin.append a b)).det.re + t * Real.log C := by
  first | exact @GlobalTheory.log_det_gram_add_le_of_adapted_frame | exact GlobalTheory.log_det_gram_add_le_of_adapted_frame | (intros; apply GlobalTheory.log_det_gram_add_le_of_adapted_frame <;> assumption)
