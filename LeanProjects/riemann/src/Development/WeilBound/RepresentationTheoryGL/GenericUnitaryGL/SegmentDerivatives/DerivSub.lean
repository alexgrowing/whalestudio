import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DerivSub : Prop :=
  ∀ (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V), IsSmooth π → HasFiniteLength π →
    Nontrivial (TwJacquet (GlobalTheory.BZMir.iterPhi k ψ j (GlobalTheory.BZMir.resM k π)).ρ (GlobalTheory.BZMir.MirUin k (n + 1)) 1) →
    ∃ (S : IrrRep (GL (Fin (n + 1)) k)) (f : S.ρ.IntertwiningMap (GlobalTheory.BZMir.deriv k ψ j π)), Function.Injective f

end GlobalTheory.BZSeg

end
