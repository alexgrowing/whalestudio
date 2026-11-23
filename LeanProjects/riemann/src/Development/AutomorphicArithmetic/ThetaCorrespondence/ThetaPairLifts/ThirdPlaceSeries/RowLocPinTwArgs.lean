import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLocalLevelCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
open scoped TensorProduct in
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.IndefR.principalLevelFrame in
theorem rowLocPin_congr_alt {D : D7} {V : HSp D} {Sp : D.what₂.Tau → SPar} (lp : Formalism.L2.LPTiedPlaceholder D)
    {θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {PY PY' : principalLevelFrame.RowPsi V D.R.r}
    {M M' : Formalism.IndefR.Mult.DSModel V Sp} {J J' : Bool → Set (GA D V)} {χ χ' : Bool → GA D V → ℂ}
    {e e' : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} {eFT : D.what₂.FT ≃ principalLevelFrame.FTR θ PY M J χ e}
    {eFT' : D.what₂.FT ≃ principalLevelFrame.FTR θ' PY' M' J' χ' e'} (hθ : θ = θ') (hP : PY = PY') (hM : M = M') (hJ : J = J')
    (hχ : χ = χ') (he : e = e') (hE : HEq eFT eFT') (h : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt lp θ PY M J χ e eFT) :
    _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt lp θ' PY' M' J' χ' e' eFT' := by
  subst hθ hP hM hJ hχ he
  cases hE
  exact h
set_option maxHeartbeats 4000000 in
theorem rowLocPin_twArgs_alt {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (lp : Formalism.L2.LPTiedPlaceholder (w.st Z).toD7)
    (hr : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt lp t.r.z.R.θ t.r.Y.PY (t.r.z.R.MY 0)
      (fun s => levS _ (t.r.z.R.βY 0) (t.r.z.R.dat0 (t.r.z.R.toRealDat.levR t.r.z.F.lv2 s)))
      (fun s => Formalism.IndefR.Lev.levChi _ (t.r.z.R.βY 0) (t.r.z.R.dat0 (t.r.z.R.toRealDat.levR t.r.z.F.lv2 s)))
      (fun _ => t.r.z.R.e0) t.r.Y.eFT) :
    _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt lp a.x.R.θ a.x.Y.PY (a.x.R.MY 0)
      (fun s => levS _ (a.x.R.βY 0) (a.x.R.dat0 (a.x.R.toRealDat.levR a.x.F.lv2 s)))
      (fun s => Formalism.IndefR.Lev.levChi _ (a.x.R.βY 0) (a.x.R.dat0 (a.x.R.toRealDat.levR a.x.F.lv2 s)))
      (fun _ => a.x.R.e0) a.x.Y.eFT := by
  have hPY := a.PY
  have hE := a.eFT
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  dsimp only at hPY hE ⊢
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, Y, _⟩ := x
  dsimp only at pack hPY hE ⊢
  cases pack
  exact _root_.GlobalTheory.Mem.Top.Bl.rowLocPin_congr_alt lp rfl (eq_of_heq hPY).symm rfl rfl rfl rfl hE.symm hr
set_option maxHeartbeats 4000000 in
theorem locPin_level_character_of_bWit : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0) (fun s => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 s))) (fun s => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 s))) (fun _ => w.x.R.e0) w.x.Y.eFT := by
  intro hL p
  apply GlobalTheory.Fc.EvP.of_all
  intro κ K _ q c b w _
  rw [show b.R.T.n.gal = q.core_data_of_point.a.all.gal from w.recPin.s.gal, ← eq_of_heq w.ax]
  exact _root_.GlobalTheory.Mem.Top.Bl.rowLocPin_twArgs_alt w.a _ q.core_data_of_point.row.rowLoc
end GlobalTheory.Mem.Top.Bl
end
