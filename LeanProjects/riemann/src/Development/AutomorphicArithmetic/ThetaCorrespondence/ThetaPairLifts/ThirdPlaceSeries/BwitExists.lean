import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLanglandsPrmReduction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServTIff
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSelectionPairLocalLanglandsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealInExistsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecInPartsExistsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelectedLowerMapThirdStageStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHostDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSideRT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelectedSideRealizationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.SelAll
theorem rpk_eq_alt {D : D7} {O : Obj D} {R : _root_.Formalism.L2.RecTAlt O.ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} (P : Formalism.L2.Rows.RowSideFamily O.ex)
    {Dc Dc' : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Sp : ∀ Zs, SPer (Dc Zs)} {Sp' : ∀ Zs, SPer (Dc' Zs)}
    {Z Z' : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {B : _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Z S} {B' : _root_.Formalism.IndefR.RealTBAlt R P Dc' Sp' Z' S}
    (h1 : Dc = Dc') (h2 : HEq Sp Sp') (h3 : Z = Z') (h4 : HEq B B') :
    (⟨P, Dc, Sp, Z, B⟩ : _root_.GlobalTheory.Mem.Top.Bl.RealPackage R S) = ⟨P, Dc', Sp', Z', B'⟩ := by
  subst h1; subst h3; cases h2; cases h4; rfl
theorem real_tb_congr_of_heq {D : D7} {O : Obj D} (R : _root_.Formalism.L2.RecTAlt O.ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (P : Formalism.L2.Rows.RowSideFamily O.ex)
    {Dc Dc' : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Sp : ∀ Zs, SPer (Dc Zs)} {Sp' : ∀ Zs, SPer (Dc' Zs)}
    {Z Z' : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    (h1 : Dc = Dc') (h2 : HEq Sp Sp') (h3 : Z = Z') :
    _root_.Formalism.IndefR.RealTBAlt R P Dc Sp Z S = _root_.Formalism.IndefR.RealTBAlt R P Dc' Sp' Z' S := by
  subst h1; subst h3; cases h2; rfl
set_option maxHeartbeats 4000000 in
theorem bwit_exists_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat) → GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) := by
  intro hG hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN hM
  refine ((GlobalTheory.Fc.EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and hM).mono ?_
  rintro κ K - ⟨hH, hMK⟩ q R hR c DH _ _
  have hMq := hMK q
  have hcols : R.T.cols = q.x.col.C := hR.s.cols
  obtain ⟨sP, sS, hP, hS⟩ : ∃ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP),
      HEq sP q.saturationAtWeightedPoint.P ∧ HEq sS q.saturationAtWeightedPoint.S := by
    rw [hcols]; exact ⟨q.saturationAtWeightedPoint.P, q.saturationAtWeightedPoint.S, HEq.rfl, HEq.rfl⟩
  have hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toRealSpectralMatching R).X u (sS.toRealSpectralMatching R).Y.hK := sP.fin.inHH
  obtain ⟨a, x, ax, C, hDc, hSp, hW', hXg, hCP, hZ, hsp, κS, sEEc, hsE, hκ, hsee⟩ :=
    _root_.GlobalTheory.T.exists_selected_realization_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS DH.1.1 DH.1.2 c hin
  obtain ⟨y, hyt, hyc, hySx, hyeF, hyfi, hyu⟩ := _root_.GlobalTheory.T.selected_realization_geometric_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax hin hsp κS sEEc hsE hκ hsee
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.T.selected_realization_side_alt hG hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax y
  have pin := _root_.GlobalTheory.T.selected_lower_map_holds_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax
  obtain ⟨HD, hHD⟩ := _root_.GlobalTheory.HostDatumExists.exists_hostDatum_alt hGAR _ _ _ _ _ _ _ _ q.O.ex R.T.toTiedDataS (GlobalTheory.Mem.Top.Bl.hostPins_wpt hRF _ _ q) q.x.pin.d3b
  have side := _root_.GlobalTheory.T.selected_side_realization_holds_alt hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hMq R hR sP sS hP hS a x ax y r HD hHD
  have h1 : C.c.face = x.F.Dc := eq_of_heq hDc
  have h3 : GlobalTheory.Fc.zsc (divisionPairOfAdelicFormsFaceColumnsData x) DH.1.1 DH.1.2 c = x.F.Zsc := hZ.symm
  have hB := _root_.GlobalTheory.Mem.R3.SelAll.real_tb_congr_of_heq R (sS.toRealSpectralMatching R) (divisionPairOfAdelicFormsFaceColumnsData x) h1 hSp h3
  have hx : Holds x.R x.F := by
    have e : a.x = x := eq_of_heq ax
    rw [← e]; exact a.intersectionNumber_baseChange
  let b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c := ⟨R, sS.toRealSpectralMatching R, divisionPairOfAdelicFormsFaceColumnsData x, pin, DH, C, cast hB.symm (_root_.GlobalTheory.Mem.R3.boundedRealisationOfInput y)⟩
  have heq : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y := _root_.GlobalTheory.Mem.R3.SelAll.rpk_eq_alt (divisionPairOfAdelicFormsFaceColumnsData x) h1 hSp h3 (cast_heq _ _)
  exact ⟨b, rfl, ⟨{ x := x, a := a, ax := ax, y := ⟨hx, y, r, heq, HD⟩, recPin := hR, s := ⟨sP, sS, hP, hS, rfl⟩, pt := ⟨hyt, hyc⟩, sx := hySx, eF := hyeF, fi := hyfi, uS := hyu, parts := hr, cW := ⟨hW', hXg⟩, d3b := heq_of_eq hHD, side := side, colPins := hCP }⟩⟩
end GlobalTheory.Mem.R3.SelAll
end
