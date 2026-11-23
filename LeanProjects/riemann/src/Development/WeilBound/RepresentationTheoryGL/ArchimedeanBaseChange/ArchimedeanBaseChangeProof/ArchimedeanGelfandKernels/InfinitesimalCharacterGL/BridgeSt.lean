import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.EopW

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.RgBcC.Bridge

def BridgeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (V : Submodule ℂ (Sm E a))
    (w : InfinitePlace E) (χ : Inf a),
    (∀ φ ∈ V, ∀ g : GA E a, IsEig χ (along w g φ.1)) ↔
      HasInfCharGL V w.embedding (Multiset.map (χ true) Finset.univ.val) ∧
        HasInfCharGL V (ComplexEmbedding.conjugate w.embedding) (Multiset.map (χ false) Finset.univ.val)

end PositivityTheory.RgBcC.Bridge
