import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.StdIrrQuotGeneric

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ProdIotaRev : Prop :=
  ∀ (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
    ∃ hd' : ∑ a, (Zc.dualCl (x (Fin.rev a))).1 = N,
      Nonempty (Representation.Equiv ((prodIrr x hd).comp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k))
        (prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hd'))

end GlobalTheory.BZSeg

end
