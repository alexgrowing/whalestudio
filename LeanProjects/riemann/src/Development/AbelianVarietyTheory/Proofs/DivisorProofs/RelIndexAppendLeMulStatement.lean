import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexAppendLeMul
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_append_le_mul : ∀ (K : Type) [Field K] [NumberField K] (m m' : ℕ) (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (W : Submodule (𝓞 K) (Fin m → K)), W.FG → ∀ (s t : ℕ) (a : Fin s → Fin m → K) (b : Fin t → Fin m → K), IsFrame K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) a → IsFrame K W (Fin.append a b) → (Submodule.span (𝓞 K) (Set.range (Fin.append a b))).toAddSubgroup.relIndex W.toAddSubgroup ≤ (Submodule.span (𝓞 K) (Set.range a)).toAddSubgroup.relIndex (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)).toAddSubgroup * (Submodule.span (𝓞 K) (Set.range (q ∘ b))).toAddSubgroup.relIndex (W.map (q.restrictScalars (𝓞 K))).toAddSubgroup := by
  first | exact @GlobalTheory.AdaptedFrameIndex.relIndex_span_append_le | exact GlobalTheory.AdaptedFrameIndex.relIndex_span_append_le | (intros; apply GlobalTheory.AdaptedFrameIndex.relIndex_span_append_le <;> assumption)
