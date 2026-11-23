import Formalism.WachLatticeTwists.TorsionKernelSplitting.TorsionKernelProofs.TheoremNFiveTopSplit
import Formalism.WachLatticeTwists.TorsionKernelSplitting.TorsionKernelProofs.TorsionLeHZero

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem IsLatSeq.res {O G T₂ V A : Type*} [CommRing O] [Group G] [AddCommGroup T₂] [Module O T₂]
    [AddCommGroup V] [Module O V] [AddCommGroup A] [Module O A]
    {ρ₂ : Representation O G T₂} {ρV : Representation O G V} {ρA : Representation O G A}
    {i : T₂ →ₗ[O] V} {q : V →ₗ[O] A} (h : IsLatSeq ρ₂ ρV ρA i q) (D : Subgroup G) :
    IsLatSeq (resRep ρ₂ D) (resRep ρV D) (resRep ρA D) i q :=
  ⟨h.1, h.2.1, fun g m => h.2.2.1 (g : G) m, fun g m => h.2.2.2 (g : G) m⟩

end Formalism.RepresentationBoundsCohomology.JS
