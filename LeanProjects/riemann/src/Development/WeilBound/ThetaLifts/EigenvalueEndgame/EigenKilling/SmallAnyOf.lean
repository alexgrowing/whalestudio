import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation

noncomputable section

namespace PositivityTheory.ThKEnd.Comp

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKG.Tow

theorem bigAny_of (hG : GenBig) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx) (hPl : PlaneHerm)
    (hC : EvCone) : BigAny := anyBig hG hA hK hS hI hP hPl hC

theorem smallAny_of (hG : GenSmall) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx) (hPl : PlaneHerm)
    (hC : EvCone) : SmallAny := anySmall hG hA hK hS hI hP hPl hC

end PositivityTheory.ThKEnd.Comp

end
