import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

def ProperKilled : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ v : Pl F,
      (∀ N, GlobalTheory.Published.ThetaSub om v N → N ≠ SB _ → N ≤ LinearMap.ker (Rf.p v)) ∧
      ∀ N, GlobalTheory.Published.ThetaSub om' v N → N ≠ SB _ → N ≤ LinearMap.ker (Rf.p' v)

end PositivityTheory.Sph

end
