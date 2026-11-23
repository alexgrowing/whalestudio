import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamCol
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColsStdOfBWit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsOfVal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkValOfBWitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqZeroOfPkAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEqAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevGBaseOfBWitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DataOfBWitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevReadOfBWitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecValPackBStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsJValSmulStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TopVal
section True
open GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
theorem to_map_pr_x_eq_pk_at (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (g : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (hg : g ∈ GfC (I.rec7 l Z).sp.X')
    (v : SmT (_root_.GlobalTheory.Fam.pk_z W).MX) :
    (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x)) v g = (_root_.GlobalTheory.Fam.pk_z W).prX (_root_.GlobalTheory.TopVal.packageAtPoint W t x g) v := by
  have h1 : (_root_.GlobalTheory.Fam.pk_z W).cX.ρ g⁻¹ = 1 := W.Q.charW.base.models.cX.1 _ (inv_mem hg)
  show (_root_.GlobalTheory.Fam.pk_z W).prX ((_root_.GlobalTheory.Fam.pk_z W).cX.ρ g⁻¹ (_root_.GlobalTheory.TopVal.packageAtPoint W t x g)) v = _
  rw [h1]
  rfl
set_option maxHeartbeats 1000000 in
theorem exists_is_j_pair_val_of_vanishing (hg : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (u : B.Word) (cv : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (hE : _root_.GlobalTheory.TopVal.ValEqvAlt W cv)
    (hP : _root_.GlobalTheory.TopVal.PackageValuation W cv)
    (hi : ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
      (∀ g y, HasMat g y → IsUni B y → _root_.GlobalTheory.TopVal.packageAtPoint W t x g = 0) → ∀ d, val φ d = 0) :
    ∃ j, IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j ∧ ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x → ∀ d v,
      (_root_.GlobalTheory.Fam.pk_z W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d) := by
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.SeeSaw.exists_isJ_of_par (GlobalTheory.SeeSaw.sg_trueColumns I l Z u) (_root_.GlobalTheory.Fam.pk_z W).MX rfl
  by_cases h0 : cv = 0
  · refine ⟨j₀, hj₀, fun t φ x hx d v => ?_⟩
    have hz := hi t φ x hx (fun g y h1 h2 => (hP t φ x hx g y h1 h2).trans (by rw [h0]; rfl)) d
    rw [hz, map_zero, map_zero, LinearMap.zero_apply]
    unfold pairVal
    rw [Submodule.coe_zero, map_zero, map_zero]
  · obtain ⟨a, ha, hJ⟩ := _root_.GlobalTheory.T.unit_gram_family_property_alt W hg u cv hE h0 j₀ hj₀
    exact ⟨a • j₀, isJ_smul hj₀ ha, fun t φ x _ d v => hJ _ v⟩
set_option maxHeartbeats 1000000 in
theorem reads_pk_alt (hOk : I.Ok) (hC : I.StdC l Z W.R.T.cols) (hW : _root_.GlobalTheory.AdForm.TwStdAlt W) (u : B.Word)
    (cv : Val B →ₛₗ[B.embLL] (_root_.GlobalTheory.Fam.pk_z W).cX.W) (hP : _root_.GlobalTheory.TopVal.PackageValuation W cv) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ))
    (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t) (hx : IsRes φ x)
    (hV : ∀ d v, (_root_.GlobalTheory.Fam.pk_z W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d))
    (G : (I.rec7 l Z).what₂.Amb (W.P.I.tup t)) (hG : RecVal u (W.P.I.tup t) φ G) :
    _root_.GlobalTheory.Fam.ReadsCoefficients W u j 1 (W.P.I.tup t) G ((_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t x))) := by
  refine _root_.GlobalTheory.TopVal.reads_of_pairVal W hC hW u j _ φ G hG _ fun g y pt v hy hp => ?_
  refine (_root_.GlobalTheory.TopVal.to_map_pr_x_eq_pk_at W t x g hy.1 v).trans ?_
  rw [hP t φ x hx g y hy hp.uni, GlobalTheory.T.decoratedLatticeOfAdelicMatrix_eq_rowPoint I hOk _ y pt hp]
  exact hV _ v
end True
set_option maxHeartbeats 2000000 in
theorem exists_read_at_pack_b_of_b_wit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt (_root_.GlobalTheory.Fam.packB_alt b) u j 1 := by
  intro hL p K q c b hW ⟨rx⟩ u
  obtain ⟨hOk, ⟨hPins⟩, -, ⟨hC⟩, hTS⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hW
  have hg := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords q.w.I hOk hPins q.w.l q.Z).2.1
  obtain ⟨cv, hE, hP⟩ := _root_.GlobalTheory.T.exists_valEqv_of_bWit_std q b hW rx.std
  obtain ⟨j, hJ, hV⟩ := _root_.GlobalTheory.TopVal.exists_is_j_pair_val_of_vanishing (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) hg u cv hE hP (_root_.GlobalTheory.T.pk_at_vanishing_of_is_uni q b hW)
  refine ⟨j, hJ, one_mem _, fun t => ⟨⟨fun h => _root_.GlobalTheory.T.level_group_reference_tuple_alt q b hW u t h,
    fun h => levG_one _ (_root_.GlobalTheory.T.mem_level_iff_twisted_class_alt q b hW u t h) (_root_.GlobalTheory.T.level_character_twisted_class_alt q b hW u t h)⟩, fun F F' hF => ?_⟩⟩
  obtain ⟨φ, hφ, hR⟩ := _root_.GlobalTheory.T.one_form_exists_heq_alt q b hW ⟨rx⟩ t F F' hF
  exact _root_.GlobalTheory.TopVal.reads_pk_alt (I := q.w.I) (l := q.w.l) (Z := q.Z) (_root_.GlobalTheory.Fam.packB_alt b) hOk hC hTS u cv hP j t φ _ hφ (hV t φ _ hφ) _ (hR u)
end GlobalTheory.TopVal
end
