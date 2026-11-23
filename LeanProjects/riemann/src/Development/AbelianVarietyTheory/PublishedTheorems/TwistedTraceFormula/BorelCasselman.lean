import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.Published

def BorelCasselman : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V),
    IsAdmissible π → Function.Bijective (iwahoriProj π)

example (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsAdmissible (detRep n χ) :=
  ⟨(isSmooth_ofChar_iff _).2 hχ.detChar, fun _ _ _ => inferInstance⟩

end GlobalTheory.Published
