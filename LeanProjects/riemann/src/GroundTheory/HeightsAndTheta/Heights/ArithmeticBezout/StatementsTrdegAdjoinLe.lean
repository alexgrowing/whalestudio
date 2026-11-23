import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def TrdegAdjoinLe.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (s : Set Ω) (ι : Type) [Fintype ι] (t : ι → Ω)
    (ι' : Type) (w : ι' → Ω), (∀ i, IsAlgebraic (Algebra.adjoin K (s ∪ Set.range t)) (w i)) →
      Algebra.trdeg K (Algebra.adjoin K (Set.range w)) ≤
        Algebra.trdeg K (Algebra.adjoin K s) + Fintype.card ι

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
