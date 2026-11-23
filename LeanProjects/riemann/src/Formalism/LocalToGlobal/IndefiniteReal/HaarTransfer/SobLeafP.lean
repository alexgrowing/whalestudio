import Mathlib

open NumberField NumberField.InfinitePlace

namespace Formalism.IndefR.Leaf.HaarTransferContinuity

variable (F : Type) [Field F] [NumberField F]

abbrev W := ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // ¬ v.IsReal} → ℂ)

noncomputable def E (x : InfiniteAdeleRing F) : W F :=
  (fun v => Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
   fun v => Completion.extensionEmbedding v.1 (x v.1))

open scoped Classical in
noncomputable def G (w : W F) : InfiniteAdeleRing F := fun v =>
  if h : v.IsReal then (Completion.isometryEquivRealOfIsReal h).symm (w.1 ⟨v, h⟩)
  else (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp h)).symm (w.2 ⟨v, h⟩)

end Formalism.IndefR.Leaf.HaarTransferContinuity
