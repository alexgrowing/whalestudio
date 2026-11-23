import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePadicGradingCompare
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_padic_grading_compare : ∀ (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime] (L L' : Submodule (𝓞 K) (Fin g → K)) (x x' : Fin g → Fin g → K) (s s' : ℕ), Full L → Full L' → L ≤ L' → (∀ i, x i ∈ L) → LinearIndependent K x → ¬ p ∣ s → (∀ v ∈ L, (s : K) • v ∈ Submodule.span (𝓞 K) (Set.range x)) → (∀ i, x' i ∈ L') → LinearIndependent K x' → ¬ p ∣ s' → (∀ v ∈ L', (s' : K) • v ∈ Submodule.span (𝓞 K) (Set.range x')) → (padicValNat p (L.toAddSubgroup.relIndex L'.toAddSubgroup) : ℤ) = padicValRat p (Algebra.norm ℚ (Matrix.of fun i k => x k i).det) - padicValRat p (Algebra.norm ℚ (Matrix.of fun i k => x' k i).det) := by
  first | exact @GlobalTheory.LocIndex.padicValNat_relIndex_eq | exact GlobalTheory.LocIndex.padicValNat_relIndex_eq | (intros; apply GlobalTheory.LocIndex.padicValNat_relIndex_eq <;> assumption)
