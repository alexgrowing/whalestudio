import Mathlib

noncomputable section

open NumberField

namespace Formalism.L2.S.Pv.PsiTrCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embOf (φ : InfinitePlace F → (E →+* ℂ)) (p : InfinitePlace F × Bool) : E →+* ℂ :=
  if p.2 then ComplexEmbedding.conjugate (φ p.1) else φ p.1

end Formalism.L2.S.Pv.PsiTrCore
