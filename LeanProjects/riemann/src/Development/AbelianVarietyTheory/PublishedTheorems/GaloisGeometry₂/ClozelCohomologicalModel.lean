import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.Published

def ClozelCohomological : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a,
    (CG.mk π).IsRegAlg → GKCoh.IsCohomological π

end GlobalTheory.Published
