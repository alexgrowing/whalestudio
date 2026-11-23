import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamCol
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColsStdOfBWit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.BaseLevel
open NumberField IsDedekindDomain GlobalTheory.Mem.Col2 Formalism.L2.Forms GlobalTheory.SeeSaw GlobalTheory.SeeSaw.TopLevel
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
set_option maxHeartbeats 2000000 in
theorem topLev_of_btw_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x)
    {u : D.what₂.Word} (K₀ : ClsPTied u) (h : PairDataBaseTupleLevelEqualsClassLevel x K₀) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (ht : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = D.what₂.mu0) :
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t))
      (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y → ∀ t : k.P.T, k.P.I.tup t = D.what₂.mu0 →
      letI := k.B.alg
      GlobalTheory.Core.Rk.Top.TopLev K₀
        (levS _ k.B.Q.Rl.toRealDat.βX (datXP k.B.Q.Rl.toRealDat (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) t))
        (levChi _ k.B.Q.Rl.toRealDat.βX (datXP k.B.Q.Rl.toRealDat (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) t)) := by
    intro k hk
    subst hk
    exact h
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq t ht
set_option maxHeartbeats 2000000 in
theorem pairDataBaseTupleLevel_eq_classLevel_of_stdF {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K)
    (a : R3.TwArgs q.O.ex q.x.what₂) (v : q.B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((q.w.D q.Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (q.w.D q.Z) v Ch chOf) (hF : TC.StdF q.w.I q.w.l q.Z v F) : PairDataBaseTupleLevelEqualsClassLevel (O := q.O) a.x F.clsP := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F' cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  intro t ht
  have hT' : Y.tup = q.x.what₂.r.Y.tup := eq_of_heq htup
  have z := q.x.what₂.r.z.lev
  have hix : R3.ixOf q.w.I _ t = q.w.I.mu0 :=
    (q.x.what₂.r.tup_ix t).symm.trans ((congrFun hT' t).symm.trans ht)
  have hQ : q.x.what₂.r.z.R.Q t = ∅ := (z.Q t).trans ((congrArg q.w.I.Q hix).trans q.w.I.twistPrimes_reference_tuple_eq_empty)
  have hc := z.is.chi
  rw [z.C] at hc
  exact topLev_levPOf q.w.I q.w.l q.Z q.w.ok q.w.pins v F hF r_le_X q.x.what₂.r.z.R.Pg (q.x.what₂.r.z.R.Q t) q.x.what₂.r.z.R.βX
    z.Pg hQ z.beta.2 q.x.what₂.r.z.R.eG q.x.what₂.r.z.idG q.x.what₂.r.z.R.chi (q.x.what₂.r.z.R.xiR t) hc
set_option maxHeartbeats 2000000 in
theorem levG_base_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((_root_.GlobalTheory.Fam.packB_alt b).R.T.cols.forms u).clsP.toG 1 (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  intro hL p K q c b hw u t ht
  obtain ⟨-, -, -, ⟨hC⟩, -⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hw
  have hx : hw.a.x = hw.x := eq_of_heq hw.ax
  exact (levG_one_iff _ _ _).2 (_root_.GlobalTheory.Fam.BaseLevel.topLev_of_btw_alt b hw.x hw.y _ (hx ▸ _root_.GlobalTheory.Fam.BaseLevel.pairDataBaseTupleLevel_eq_classLevel_of_stdF q hw.a u _ (hC u)) t ht)
end GlobalTheory.Fam.BaseLevel
end
end
