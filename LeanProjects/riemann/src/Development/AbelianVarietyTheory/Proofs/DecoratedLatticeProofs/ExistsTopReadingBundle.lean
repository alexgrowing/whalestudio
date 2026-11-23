import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColsStdOfBWit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingOfSg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTupleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffTwistedClassStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTwistedClassStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopValueWitnessStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneFormExistsHeqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniformStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedLatticeOfAdelicMatrixEqRowPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemmaStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal

theorem isJ_smul {D : D7} {u : D.what₂.Word} {S : D.what₂.Tau → SPar} {M : Formalism.IndefR.Mult.DSModel D.sp.X' S}
    {j : SmT M →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)} (h : GlobalTheory.Core.Rk.Top.IsJ u M j) {a : ℂ} (ha : a ≠ 0) :
    GlobalTheory.Core.Rk.Top.IsJ u M (a • j) where
  inj := fun _ _ e => h.inj (smul_right_injective _ ha e)
  range := (LinearMap.range_smul j a ha).trans h.range
  eqv := fun τ g hg v w hw y y' hy => congrArg (a * ·) (h.eqv τ g hg v w hw y y' hy)

section True

open GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex)

theorem toMap_fin (t : W.P.T) (x : W.P.A3.A.fam.amb.FR t) (g : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (hg : g ∈ GfC (I.rec7 l Z).sp.X')
    (v : SmT (pk W).MX) :
    (pk W).cX.toMap (pk W).prX (((pk W).HX t).e ((pk W).jX t x)) v g = (pk W).prX (pkAt W t x g) v := by
  have h1 : (pk W).cX.ρ g⁻¹ = 1 := W.Q.charW.base.models.cX.1 _ (inv_mem hg)
  show (pk W).prX ((pk W).cX.ρ g⁻¹ (pkAt W t x g)) v = _
  rw [h1]
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_j (hg : Formalism.L2.Forms.gramP (I.rec7 l Z) = 1) (u : B.Word) (cv : Val B →ₛₗ[B.embLL] (pk W).cX.W) (hE : ValEqv W cv)
    (hP : PkVal W cv)
    (hi : ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x →
      (∀ g y, HasMat g y → IsUni B y → pkAt W t x g = 0) → ∀ d, val φ d = 0) :
    ∃ j, IsJ u (pk W).MX j ∧ ∀ (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t), IsRes φ x → ∀ d v,
      (pk W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d) := by
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.SeeSaw.exists_isJ_of_par (GlobalTheory.SeeSaw.sg_trueColumns I l Z u) (pk W).MX rfl
  by_cases h0 : cv = 0
  · refine ⟨j₀, hj₀, fun t φ x hx d v => ?_⟩
    have hz := hi t φ x hx (fun g y h1 h2 => (hP t φ x hx g y h1 h2).trans (by rw [h0]; rfl)) d
    rw [hz, map_zero, map_zero, LinearMap.zero_apply]
    unfold pairVal
    rw [Submodule.coe_zero, map_zero, map_zero]
  · obtain ⟨a, ha, hJ⟩ := GlobalTheory.T.unit_gram_family_property W hg u cv hE h0 j₀ hj₀
    exact ⟨a • j₀, isJ_smul hj₀ ha, fun t φ x _ d v => hJ _ v⟩

set_option maxHeartbeats 1000000 in

theorem reads_pk (hOk : I.Ok) (hC : I.StdC l Z W.R.T.cols) (hW : GlobalTheory.AdForm.TwStd W) (u : B.Word)
    (cv : Val B →ₛₗ[B.embLL] (pk W).cX.W) (hP : PkVal W cv) (j : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ))
    (t : W.P.T) (φ : Frm I (W.P.I.tup t)) (x : W.P.A3.A.fam.amb.FR t) (hx : IsRes φ x)
    (hV : ∀ d v, (pk W).prX (cv (val φ d)) v = pairVal B (j v) (val φ d))
    (G : (I.rec7 l Z).what₂.Amb (W.P.I.tup t)) (hG : RecVal u (W.P.I.tup t) φ G) :
    Reads W u j 1 (W.P.I.tup t) G ((pk W).cX.toMap (pk W).prX (((pk W).HX t).e ((pk W).jX t x))) := by
  refine reads_of_val W hC hW u j _ φ G hG _ fun g y pt v hy hp => ?_
  refine (toMap_fin W t x g hy.1 v).trans ?_
  rw [hP t φ x hx g y hy hp.uni, GlobalTheory.T.decoratedLatticeOfAdelicMatrix_eq_rowPoint I hOk _ y pt hp]
  exact hV _ v

end True

theorem levG_one {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad} (K : Formalism.L2.Forms.ClassesAtPrimes M bad)
    {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ} (h1 : ∀ g, g ∈ J ↔ ∃ κ : K.lev.U, GlobalTheory.Core.Rk.Top.HasMat g κ.1)
    (h2 : ∀ g (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → χ g = star ((K.lev.chi κ : ℂˣ) : ℂ)) : LevG K 1 J χ := by
  simp only [LevG, inv_one, one_mul, mul_one]
  exact ⟨h1, h2⟩

set_option maxHeartbeats 2000000 in

theorem topReadAt_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → Nonempty (Bl.RXs q.x.what₂) → ∀ u, ∃ j, TopReadAt (packB b) u j 1 := by
  intro hL p K q c b hW ⟨rx⟩ u
  obtain ⟨hOk, ⟨hPins⟩, -, ⟨hC⟩, hTS⟩ := GlobalTheory.Fam.colsStd_of_bWit q b hW
  have hg := (GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords q.w.I hOk hPins q.w.l q.Z).2.1
  obtain ⟨cv, hE, hP⟩ := GlobalTheory.T.exists_top_value_witness q b hW rx.std
  obtain ⟨j, hJ, hV⟩ := exists_j (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) hg u cv hE hP (GlobalTheory.T.top_value_vanishing_uniform q b hW)
  refine ⟨j, hJ, one_mem _, fun t => ⟨⟨fun h => GlobalTheory.T.level_group_reference_tuple q b hW u t h,
    fun h => levG_one _ (GlobalTheory.T.mem_level_iff_twisted_class q b hW u t h) (GlobalTheory.T.level_character_twisted_class q b hW u t h)⟩, fun F F' hF => ?_⟩⟩
  obtain ⟨φ, hφ, hR⟩ := GlobalTheory.T.one_form_exists_heq q b hW ⟨rx⟩ t F F' hF
  exact reads_pk (I := q.w.I) (l := q.w.l) (Z := q.Z) (packB b) hOk hC hTS u cv hP j t φ _ hφ (hV t φ _ hφ) _ (hR u)

end GlobalTheory.TopVal
