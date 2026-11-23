import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormClassSumMatrixLeCauchySchwarz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_norm_classSumMatrix_le_cauchySchwarz : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t h h' : ℝ), 0 ≤ t → 0 ≤ h → 0 ≤ h' → (∀ b, PosAt ((Q.F i).mem b) v) → (∀ b, PosAt ((Q.F (i + 1)).mem b) v) → (∀ b, (Nat.card ((Q.F i).mem b).Cl : ℝ) ≤ h) → (∀ b, (Nat.card ((Q.F (i + 1)).mem b).Cl : ℝ) ≤ h') → (∀ b b' d d', OpLe ((Q.F i).mem b) ((Q.F (i + 1)).mem b') v ((Q.kk i b b').k d d') t) → ∀ φ : (Q.F i).Forms, (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤ (Fintype.card (Q.F i).β : ℝ) * (Fintype.card (Q.F (i + 1)).β : ℝ) * h * h' * t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
  first | exact @GlobalTheory.ColNorms.SumBound.step_le | exact GlobalTheory.ColNorms.SumBound.step_le | (intros; apply GlobalTheory.ColNorms.SumBound.step_le <;> assumption)
