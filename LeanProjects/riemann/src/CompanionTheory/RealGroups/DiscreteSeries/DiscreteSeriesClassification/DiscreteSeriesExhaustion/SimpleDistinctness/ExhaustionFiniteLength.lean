import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfCommute
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimensionalComapSubtype
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GoodPathReplicate
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PathEndEqAddNat
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleDistinct
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfSeparatingSmoothL2Maps
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitarizableOfSeparatingSmoothL2Maps
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsWeightOfIntertwine
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsIsoOfHighest
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestRenumber
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContinuousUnitsRenSymm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestOfPerm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KModOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniqueParam
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharOfScalChar

namespace CompanionTheory.RgExh.Fin

theorem exhaustion_finite_length : CompanionTheory.RgExh.Finish :=
  GlobalTheory.CompanionTheory.RgExhFin.finish (GlobalTheory.CompanionTheory.RgStart.startMod : StartMod)
    (GlobalTheory.CompanionTheory.RgSteps.pathFin : PathFin)
    (GlobalTheory.CompanionTheory.RgPath.pathExists : PathExists)
    (GlobalTheory.CompanionTheory.RgPath.pathEndNat : PathEndNat)
    (GlobalTheory.CompanionTheory.RgExhFin.simpleDistinct : SimpleDistinct)
    (GlobalTheory.CompanionTheory.AdjointSignNormality.scalar_of_separating_smooth_l2_maps : ScalarCharacterOfL2Embedding)
    (GlobalTheory.CompanionTheory.RgExhFin.unitarizable_of_separating_smooth_l2_maps : UnitarizableOfL2Embedding)
    (GlobalTheory.CompanionTheory.RgIso.isoFacts : IsoFacts)
    (GlobalTheory.CompanionTheory.CharOfLowK.charOfAlgDS : CharOfAlgDS)
    (GlobalTheory.CompanionTheory.LowestDataIso.algUniq : AlgUniq)
    (GlobalTheory.CompanionTheory.LowestData.dataUniq : DataUniq)
    (GlobalTheory.CompanionTheory.RenumDS.dsOfArr : DSOfArr)
    (GlobalTheory.CompanionTheory.DSData.dsOfData : DSOfData)
    (GlobalTheory.CompanionTheory.KModOfStep.kModOf : KModOf)
    (GlobalTheory.CompanionTheory.ArrCount.arrCount : ArrCount)

end CompanionTheory.RgExh.Fin
