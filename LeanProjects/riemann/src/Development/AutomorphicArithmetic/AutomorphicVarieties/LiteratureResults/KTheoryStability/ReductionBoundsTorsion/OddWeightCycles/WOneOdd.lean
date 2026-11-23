import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockEvaluationBounds

open BlockInvariants

def WOneOdd : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N q : ℕ) (x : Pat L q), Odd q → ncyc x.1 = 1 →
    ∃ (r : ℝ) (w : InfinitePlace L), AT (N := N) x =
      r • (AT (N := N) ((finRotate q, fun _ => w, false) : Pat L q) +
        AT (N := N) ((finRotate q, fun _ => w, true) : Pat L q))

def WRot : Prop := ∀ q : ℕ, 0 < q → ncyc (finRotate q) = 1

end PositivityTheory.KB.BlockEvaluationBounds

end
