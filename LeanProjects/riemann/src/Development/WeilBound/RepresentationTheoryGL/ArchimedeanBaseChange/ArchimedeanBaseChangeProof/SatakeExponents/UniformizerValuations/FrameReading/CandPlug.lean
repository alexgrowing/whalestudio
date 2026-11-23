import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PCandLh
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PairDoubleCosetFiniteSupport
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.RExpReadOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.IsOpenChiMu
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.RReadLev
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Imports

namespace PositivityTheory.Rg.BcB.F.CandPlug

open PositivityTheory.Rg.BcB.F

theorem readT : Tail.ReadT := Tail.rReadT RS.reading_module_holds
theorem expRead : Tail.ExpRead := Tail.rExpRead PositivityTheory.Rg.BcB.N3.Final.n3
theorem readLev : Tail.ReadLev := GlobalTheory.T.real_read_levi RS.reading_module_holds RS.join_module_holds
theorem readS : Tail.ReadS := Tail.rReadS_c RS.reading_module_holds RS.join_module_holds PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

theorem candT : CandT := fun hR E _ _ _ hE n _ π _ S T F₀ F _ i s₁ s₂ Pa Pb D A G hc hG hl hne w hw hu hs =>
  PCandLh.inert_d readT expRead RS.joinSat_holds hR E hE n π S T F₀ F i s₁ s₂ Pa Pb D A G hc hG hl hne w (F.T_le w hw hu hs)

theorem candTOut : CandTOut :=
  candTOut_of (candS_of readS) candT (PCandLh.candLev_of readLev readT expRead RS.joinSat_holds)

end PositivityTheory.Rg.BcB.F.CandPlug
