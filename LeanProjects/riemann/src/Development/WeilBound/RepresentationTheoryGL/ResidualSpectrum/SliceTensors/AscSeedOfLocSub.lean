import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscAllOfRest
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStep
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsOpenStabTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatAsc
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatHerm
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PLocDual
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.CharZeroCompletion
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity

namespace PositivityTheory.Rg.Rs

theorem ascAll_holds : AscAll := by
  exact ascAll_of_rest (slice_of dict_holds finTr_holds) pr_holds indMap_holds
    (stringStep_of PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity PositivityTheory.AdelicQuotientData.jacquetShalika.2 infInd2_holds infAsc_holds
      satInd2_holds satAsc_holds satHerm_holds gap_holds)

theorem ascSeed_of_locSub (h : LocSub) : AscSeed := by
  exact ⟨ascAll_holds, C3.clause3Asc_holds h locDual_holds⟩

end PositivityTheory.Rg.Rs
