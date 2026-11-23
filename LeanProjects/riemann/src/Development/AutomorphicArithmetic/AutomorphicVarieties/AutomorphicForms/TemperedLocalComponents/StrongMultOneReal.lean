import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.UnitTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ColConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.RowStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SchOfClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SchTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.HalfBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PftDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PftMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.BetaSch
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.BetaInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ArchStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LinChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ArchKir
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.AvgChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocKir
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PsiLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PsiInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CornerIsY
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.FinKir
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.MemIffLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.AwayInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LevelS
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.DenseAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.WhBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.WlNiceZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ChartCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ConvCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ConvFub
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ConvNice
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SeedConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.IsYBlockGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigOfSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ChartSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Vanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Seed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.InKSMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PrSLocNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.InnerZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthTr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CentLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CentEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CenSame
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.TwistRed

open UpperTheory.V.Af.Smo in
theorem UpperTheory.V.Af.strongMultOneReal :
    UpperTheory.V.Published.StrongMultOneReal := by
  have hTwistRed : TwistRed := twistRed
  have hCentLoc : CentLoc := centLoc
  have hAwayInd : AwayInd := awayInd
  have hDenseAway : DenseAway := denseAway
  have hCentEq : CentEq := centEq hCentLoc hAwayInd hDenseAway
  have hPsiLoc : PsiLoc := psiLoc
  have hLevelS : LevelS := levelS
  have hSetUp : SetUp := setUp hPsiLoc hLevelS
  have hEigOfSat : EigOfSat := eigOfSat
  have hCenSame : CenSame := cenSame hCentEq hSetUp hEigOfSat
  have hWhBasic : WhBasic := whBasic
  have hChartCont : ChartCont := chartCont
  have hSeedConv : SeedConv := seedConv hChartCont
  have hSeed : Seed := seed hWhBasic hSeedConv
  have hColConj : ColConj := colConj
  have hRowStep : RowStep := rowStep
  have hSchOfClosed : SchOfClosed := schOfClosed
  have hSchTensor : SchTensor := schTensor hSchOfClosed
  have hSchTw : SchTw := schTw hSchTensor
  have hPftDeriv : PftDeriv := pftDeriv
  have hPftMul : PftMul := pftMul
  have hPftSch : PftSch := pftSch_of hSchOfClosed hPftDeriv hPftMul
  have hBetaSch : BetaSch := betaSch hPftSch
  have hBetaInt : BetaInt := betaInt
  have hArchStep : ArchStep := archStep hSchTw hPftSch hBetaSch hBetaInt
  have hLinChange : LinChange := linChange
  have hArchKir : ArchKir := archKir hColConj hRowStep hArchStep hLinChange
  have hAvgChar : AvgChar := avgChar
  have hLocDual : LocDual := locDual
  have hLocStep : LocStep := locStep hAvgChar hLocDual
  have hLocKir : LocKir := locKir hColConj hRowStep hLocStep
  have hEmbY : EmbY := embY
  have hFinKir : FinKir := finKir hLocKir hPsiLoc hEmbY
  have hPsiInf : PsiInf := psiInf
  have hKillP : KillP := killP hArchKir hFinKir hEmbY hPsiInf hChartCont
  have hSphDict : SphDict := sphDict
  have hTjSet : TjSet := tjSet hSphDict
  have hSphZero : SphZero := sphZero hSphDict hTjSet hCentLoc
  have hSphAll : SphAll := sphAll hAwayInd hSphZero hEmbY
  have hInjP : InjP := injP
  have hEigMap : EigMap := eigMap hChartCont
  have hVanish : Vanish := vanish hSphAll hInjP hDenseAway hWhBasic hEigMap
  have hWhLin : WhLin := whLin
  have hConvCont : ConvCont := convCont hChartCont
  have hConvFub : ConvFub := convFub hChartCont
  have hConvNice : ConvNice := convNice hConvCont hConvFub
  have hPair : Pair := pair hSeed hSetUp hKillP hVanish hWhBasic hWhLin hConvNice hEigOfSat hEigMap
  have hInnerZero : InnerZero := innerZero
  have hOrthTr : OrthTr := orthTr
  have hOrthStep : OrthStep := orthStep hChartCont
  have hOrthConv : OrthConv := orthConv hOrthStep hConvCont
  exact smo_of UpperTheory.V.Af.Gk.unitTwist hTwistRed hCenSame hPair hInnerZero hOrthTr hOrthConv
