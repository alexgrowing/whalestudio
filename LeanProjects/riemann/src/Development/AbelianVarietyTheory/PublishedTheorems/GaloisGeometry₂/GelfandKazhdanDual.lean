import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.Published

def GelfandKazhdanDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : CuspSub E n), Paired π π invTOp

end GlobalTheory.Published

end
