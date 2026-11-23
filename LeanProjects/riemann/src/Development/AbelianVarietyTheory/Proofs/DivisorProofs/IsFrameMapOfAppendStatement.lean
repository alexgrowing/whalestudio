import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameMapOfAppend
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrame_map_of_append : ∀ (K : Type) [Field K] [NumberField K] (m m' : ℕ) (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (W : Submodule (𝓞 K) (Fin m → K)) (s t : ℕ) (a : Fin s → Fin m → K) (b : Fin t → Fin m → K), IsFrame K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) a → IsFrame K W (Fin.append a b) → IsFrame K (W.map (q.restrictScalars (𝓞 K))) (q ∘ b) := by
  first | exact @GlobalTheory.isFrame_map_of_append_frame | exact GlobalTheory.isFrame_map_of_append_frame | (intros; apply GlobalTheory.isFrame_map_of_append_frame <;> assumption)
