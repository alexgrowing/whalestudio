import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.MinNew
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripFub
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TailFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.FdNull
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolumeOpenPosUpperHalfPlane
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIntAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.FdCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.UnfMMp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RowBij
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RowRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Unfold
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.GcdSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NsqPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.KerLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.KerDiff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NotSummableTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.OneLeNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ZLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ZInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.HalfLeIm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.IntOnOfBdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ClsExKey
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ClsProp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.LBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NicePet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.PetChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.LineExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.MelSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RankSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Rankin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ArFact
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ArSumTerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Deplete
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.Descend2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.LowTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.HolTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CuspZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.SatHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.HermOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EigOfLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.UnitTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EvPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.NewHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.PolyInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.PetRe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.CharEq2

theorem UpperTheory.V.Af.repNewform :
    UpperTheory.V.Published.RepNewform := by
  have hVolMap : UpperTheory.V.Af.Rs.VolMap := UpperTheory.V.Af.Rs.volMap
  have hStripFub : UpperTheory.V.Af.Rs.StripFub := UpperTheory.V.Af.Rs.stripFub hVolMap
  have hStripIm : UpperTheory.V.Af.Rs.StripIm := UpperTheory.V.Af.Rs.stripIm hVolMap
  have hFdFin : UpperTheory.V.Af.Rs.FdFin := UpperTheory.V.Af.Rs.fdFin hStripIm hVolMap
  have hFdNull : UpperTheory.V.Af.Rs.FdNull := UpperTheory.V.Af.Rs.fdNull hVolMap
  have hFdPos : UpperTheory.V.Af.Rs.FdPos := UpperTheory.V.Af.Rs.fdPos hVolMap
  have hStripInt : UpperTheory.V.Af.Rs.StripInt := UpperTheory.V.Af.Rs.stripInt hStripIm
  have hFdCount : UpperTheory.V.Af.Rs.FdCount := UpperTheory.V.Af.Rs.fdCount hFdNull
  have hUnfM : UpperTheory.V.Af.Rs.UnfM := UpperTheory.V.Af.Rs.unfM hFdFin hFdCount
  have hRowBij : UpperTheory.V.Af.Rs.RowBij := UpperTheory.V.Af.Rs.rowBij
  have hRowRep : UpperTheory.V.Af.Rs.RowRep := UpperTheory.V.Af.Rs.rowRep
  have hUnfold : UpperTheory.V.Af.Rs.Unfold := UpperTheory.V.Af.Rs.unfold hFdFin hUnfM hRowBij
  have hGcdSum : UpperTheory.V.Af.Rs.GcdSum := UpperTheory.V.Af.Rs.gcdSum
  have hKerBd : UpperTheory.V.Af.Rs.KerBd := UpperTheory.V.Af.Rs.kerBd
  have hKerLow : UpperTheory.V.Af.Rs.KerLow := UpperTheory.V.Af.Rs.kerLow
  have hKerDiff : UpperTheory.V.Af.Rs.KerDiff := UpperTheory.V.Af.Rs.kerDiff
  have hWTop : UpperTheory.V.Af.Rs.WTop := UpperTheory.V.Af.Rs.wTop
  have hZDiff : UpperTheory.V.Af.Rs.ZDiff := UpperTheory.V.Af.Rs.zDiff hKerBd hKerDiff hWTop
  have hZLow : UpperTheory.V.Af.Rs.ZLow := UpperTheory.V.Af.Rs.zLow hKerBd hKerLow hWTop
  have hZInt : UpperTheory.V.Af.Rs.ZInt := UpperTheory.V.Af.Rs.zInt hFdFin hKerBd hWTop
  have hSwap : UpperTheory.V.Af.Rs.Swap := UpperTheory.V.Af.Rs.swap hFdFin hKerBd hWTop
  have hTBdd : UpperTheory.V.Af.Rs.TBdd := UpperTheory.V.Af.Rs.tBdd hFdFin hZDiff hZInt
  have hTTop : UpperTheory.V.Af.Rs.TTop := UpperTheory.V.Af.Rs.tTop hFdFin hFdPos hWTop hZDiff hZLow hZInt
  have hClsEx : UpperTheory.V.Af.Rs.ClsEx := UpperTheory.V.Af.Rs.clsEx hRowBij
  have hClsProp : UpperTheory.V.Af.Rs.ClsProp := UpperTheory.V.Af.Rs.clsProp hRowRep
  have hLBd : UpperTheory.V.Af.Rs.LBd := UpperTheory.V.Af.Rs.lBd
  have hNicePet : UpperTheory.V.Af.Rs.NicePet := UpperTheory.V.Af.Rs.nicePet
  have hPetChar : UpperTheory.V.Af.Rs.PetChar := UpperTheory.V.Af.Rs.petChar
  have hPars : UpperTheory.V.Af.Rs.Pars := UpperTheory.V.Af.Rs.pars
  have hMelSum : UpperTheory.V.Af.Rs.MelSum := UpperTheory.V.Af.Rs.melSum
  have hRankSum : UpperTheory.V.Af.Rs.RankSum := UpperTheory.V.Af.Rs.rankSum hStripFub hStripInt hNicePet hPars hMelSum
  have hRankin : UpperTheory.V.Af.Rs.Rankin := UpperTheory.V.Af.Rs.rankin hStripFub hStripInt hNicePet hPars hRankSum
  have hArFact : UpperTheory.V.Af.Rs.ArFact := UpperTheory.V.Af.Rs.arFact
  have hArSum : UpperTheory.V.Af.Rs.ArSum := UpperTheory.V.Af.Rs.arSum
  have hCmp : UpperTheory.V.Af.Rs.Cmp := UpperTheory.V.Af.Rs.cmp hRankSum hRankin hArFact hArSum
  have hDeplete : UpperTheory.V.Af.Rs.Deplete := UpperTheory.V.Af.Rs.deplete
  have hSl2Two : UpperTheory.V.Af.Rn.Sl2Two := UpperTheory.V.Af.Rn.sl2Two
  have hLowTwo : UpperTheory.V.Af.Rn.LowTwo := UpperTheory.V.Af.Rn.lowTwo hSl2Two
  have hHolTwo : UpperTheory.V.Af.Rn.HolTwo := UpperTheory.V.Af.Rn.holTwo hLowTwo
  have hNoLow : UpperTheory.V.Af.Rn.NoLow := UpperTheory.V.Af.Rn.noLow UpperTheory.V.Af.Rn.centChar
  have hSatHerm : UpperTheory.V.Af.Rn.SatHerm := UpperTheory.V.Af.Rn.satHerm
  have hHermOf : UpperTheory.V.Af.Rn.HermOf := UpperTheory.V.Af.Rn.hermOf
  have hEigOfLow : UpperTheory.V.Af.Rn.EigOfLow := UpperTheory.V.Af.Rn.eigOfLow UpperTheory.V.Af.Rn.centChar
  have hUnitTw : UpperTheory.V.Af.Rn.UnitTw := UpperTheory.V.Af.Rn.unitTw
  have hEvPl : UpperTheory.V.Af.Rn.EvPl := UpperTheory.V.Af.Rn.evPl
  have hNewHerm : UpperTheory.V.Af.Rn.NewHerm := UpperTheory.V.Af.Rn.newHerm UpperTheory.V.Af.newformRep hUnitTw hHermOf hSatHerm
  have hPolyInj : UpperTheory.V.Af.Rn.PolyInj := UpperTheory.V.Af.Rn.polyInj
  have hTEq : UpperTheory.V.Af.Rs.TEq := UpperTheory.V.Af.Rs.tEq hRowBij hStripInt hUnfold hGcdSum hKerBd hSwap hLBd
  have hCore : UpperTheory.V.Af.Rs.Core := UpperTheory.V.Af.Rs.core hTBdd hTTop hClsEx hClsProp hTEq hLBd hNicePet hPetChar hCmp
  have hCharEq2 : UpperTheory.V.Af.Rs.CharEq2 := UpperTheory.V.Af.Rs.charEq2 hCore hDeplete
  exact UpperTheory.V.Af.Rn.repNewform_of
    (UpperTheory.V.Af.Rn.newAE_of hUnitTw hHermOf (UpperTheory.V.Af.Rn.holAll_of UpperTheory.V.Br.holVec hHolTwo hNoLow) hEigOfLow hSatHerm hEvPl hNewHerm
      UpperTheory.V.Br.minNew hCharEq2)
    hEvPl hPolyInj (fun w => (UpperTheory.V.Af.Nf.places w).1.pos) UpperTheory.V.Af.newformRep UpperTheory.V.Af.strongMultOneReal
