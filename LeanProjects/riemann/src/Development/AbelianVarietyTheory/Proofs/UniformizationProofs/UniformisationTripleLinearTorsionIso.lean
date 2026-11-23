import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionDegenerationLinearUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundleStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PELOfUnif

theorem exists_oAct {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (P' : PolAV S') (g : P'.A.left ⟶ G.left) (hg : IsGrpPullback P'.A G f g)
    (hw : LBIso P'.L (L.pull g)) {O : Type} [CommRing O] [StarRing O] (o : RingAct G O)
    (adj : ∀ a, LBIso (cubeLB G ![fst G G ≫ o.act a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ o.act (star a)] L)) :
    ∃ o' : P'.OAct O, ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left := by
  have inj : ∀ {T : Over S'} {x y : T ⟶ P'.A}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (P'.A ⟶ P'.A) := fun a => Over.homMk (hg.1.lift (g ≫ (o.act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ (o.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ P'.A) a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ o.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ P'.A), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  obtain ⟨w, gw'⟩ := hw
  refine ⟨⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩,
    fun a s => ?_⟩, ha⟩
  · have := o.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, o.map_one, Category.comp_id]
  · rw [← Category.id_comp (act (a * b)), pa, pa, ← Category.id_comp (act b), pa, o.map_mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act b)).symm
    rw [← Category.id_comp (act (a + b)), ← Category.id_comp (act a), ← Category.id_comp (act b), pa, pa, pa, o.map_add]
    exact MonObj.comp_mul _ _ _
  · obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati hL _ _ (adj a)
    let V : (P'.A ⊗ P'.A).left.Opens := (P'.A ⊗ P'.A).hom ⁻¹ᵁ ⊤
    let T' : Over S' := Over.mk (V.ι ≫ (P'.A ⊗ P'.A).hom)
    let j : T' ⟶ P'.A ⊗ P'.A := Over.homMk V.ι rfl
    let m := lift (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _))
    obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := fun i => (V.ι ≫ rosatiφ P'.A (act a) (act (star a)) i) ≫ g)
      (ε' := rosatiε) (fun W _ k => by
        have p₁ := prod_ros (o.act a) (o.act (star a)) (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _)) k
        have p₂ := prod_ros (act a) (act (star a)) (j ≫ fst _ _) (j ≫ snd _ _) (fun q => k (q ≫ g))
        rw [← comp_lift, lift_fst_snd, Category.comp_id] at p₂
        rw [← pa, ← pa, ← pm, ← pm] at p₁
        exact p₁.trans p₂.symm) (LB.pullGen L _ _ t m.left) (pullGen_isGen _ _ _ _ ht m.left)
    exact ⟨⊤, trivial, exists_down ((isGen_iff w).1 gw') hL P'.isLB t' ht'⟩

theorem exists_oAct_unif {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [CommRing O] [StarRing O] (o : RingAct G O)
    (adj : ∀ a, LBIso (cubeLB G ![fst G G ≫ o.act a, snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ o.act (star a)] U.LG.L)) :
    ∃ o' : A.OAct O, ∀ a, (Over.pullback (jK R)).map (o.act a) ≫ U.gen.hom = U.gen.hom ≫ o'.act a := by
  have := U.gen_hom
  have gp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) := by
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr
      (Category.id_comp _) rfl
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hig : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have hw : LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
    LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
  obtain ⟨o', ho'⟩ := exists_oAct U.LG.isLB A _ gp hw o adj
  refine ⟨o', fun a => Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩
  have a₁ : ((Over.pullback (jK R)).map (o.act a)).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ (o.act a).left := pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, ho', reassoc_of% hig, Category.assoc,
    reassoc_of% hig, a₁]

theorem w0_mul_bar_w0_eq_d_add_one_div_four {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) :
    H.w0 * H.bar H.w0 = (((H.d + 1) / 4 : ℕ) : NumberField.RingOfIntegers E) := by
  obtain ⟨m, hm⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have e : (H.d + 1) / 4 = m := by omega
  have hm' : (H.d : NumberField.RingOfIntegers E) + 1 = 4 * m := by exact_mod_cast hm
  rw [e, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]
  have h4 : (4 : NumberField.RingOfIntegers E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  linear_combination (-(2 * H.w0 + H.rt - 1)) * H.two_weight_eq_one_add_root - H.rt_sq + hm'

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : Unif I D A t.G), U.LG = t.PP → ∃ P : PELUnif I t, P.D = D ∧ P.A = A ∧ HEq P.U U ∧ P.TorsionIso := by
  intro hL h₁ h₂ h₃ h₄ E _ _ _ H R _ _ _ I hR t D A U hU
  letI := H.starRing
  have adj : ∀ a, LBIso (cubeLB t.G ![fst t.G t.G ≫ t.act.toRingAct.act a, snd t.G t.G] U.LG.L)
      (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.toRingAct.act (star a)] U.LG.L) := by
    rw [hU]; exact t.adj
  have prim : LBIso U.LG.L (cubeLB t.G ![𝟙 t.G, t.act.toRingAct.act H.w0] U.LG.L) := by
    rw [hU]; exact t.prim
  obtain ⟨oA, hA⟩ := exists_oAct_unif U.toUnifPre t.act.toRingAct adj
  obtain ⟨md, oD, lin⟩ := GlobalTheory.T.exists_ring_action_degeneration_linear_uniformisation hL h₁ h₂ h₃ h₄ R I hR D A t.G t.semi U _ oA t.act.toRingAct hA adj
  have hd := H.d_mod
  have w0 := GlobalTheory.T.psiFunction_eq_theta_of_primitive_lineBundle hL h₁ h₂ h₃ h₄ R I hR D A t.G t.semi U _ oD oA t.act.toRingAct lin adj H.w0 ((H.d + 1) / 4)
    (by show H.w0 + H.bar H.w0 = 1; rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]) (w0_mul_bar_w0_eq_d_add_one_div_four H) (by omega)
    (Nat.even_iff.2 (by omega)) prim
  let P : PELUnif I t := { D := D, mod := md, oD := oD, A := A, oA := oA, U := U, bundle := hU, lin := lin, w0 := w0 }
  exact ⟨P, rfl, rfl, HEq.rfl, GlobalTheory.UT.torsionIso_of_pelUnif hL h₁ h₂ h₃ h₄ E H R I hR t P⟩

end GlobalTheory.PELOfUnif

end
