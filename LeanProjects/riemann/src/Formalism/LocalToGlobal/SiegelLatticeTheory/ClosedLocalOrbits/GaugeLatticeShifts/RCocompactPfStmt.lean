import Mathlib

namespace Formalism.L2.SG.Pf.RCoc

def KerBaseChange : Prop :=
  ∀ (K L : Type) [Field K] [Field L] (f : K →+* L) (m p : Type) [Fintype m] [Fintype p] [DecidableEq p]
    (A : Matrix m p K), ∃ P : Matrix p p K, A * P = 0 ∧
      ∀ z : p → L, (A.map f).mulVec z = 0 → (P.map f).mulVec z = z

end Formalism.L2.SG.Pf.RCoc
