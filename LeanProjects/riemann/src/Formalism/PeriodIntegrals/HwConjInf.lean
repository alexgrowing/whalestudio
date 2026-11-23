import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut

noncomputable section

open NumberField

namespace PI.HwConjInf

open Formalism.L2.NG

def Stmt : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (τ : L →+* ℂ) (lam lam' : Fin n → ℤ),
    a.HWAt τ lam → a.HWAt (ComplexEmbedding.conjugate τ) lam' → infOf lam' = (infOf lam).map Neg.neg

end PI.HwConjInf
