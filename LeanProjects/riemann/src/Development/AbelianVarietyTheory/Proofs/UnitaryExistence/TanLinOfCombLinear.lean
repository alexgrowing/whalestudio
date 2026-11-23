import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReFrameIffReframeIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointFieldFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReframeCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.GeneralizedScalarsNumberField
open Formalism.L2.PjFree (FrBaseChg ReFrame XoNumPt TanLin SClause IntRebase)

export GlobalTheory.ReframeClauses (isPullback_dualMap epi_dualMap isCombAt_bc isTanAt_of_isCombAt isEigAt_of_isCombAt id_appLE_apply
  same_point_of_sClause sClause_iff isUnit_of_genScal frBaseChg_iff reFrame_iff
  reFrame_iff_reframeIntegral xoNumPt_iff tanLin_iff LieRebase intRebase_iff IntFrLieGL intLieGL_iff
  valV_unit intDiagUnit_of_intFrameGL first_integral coord_integral intFrLieGL_of)

section Abstract

variable {R Γ : Type} [CommRing R] [Group Γ] (sm : R → Γ →* Γ) (hmm : ∀ a b v, sm a (sm b v) = sm (a * b) v)
  (h1 : ∀ v, sm 1 v = v) (hadd : ∀ v, sm 0 v = 1 → ∀ a b, sm (a + b) v = sm a v * sm b v)

include h1 hadd in

theorem commute_of_scalars {u v : Γ} (hu : sm 0 u = 1) (hv : sm 0 v = 1) : u * v = v * u := by
  have h := hadd (u * v) (by rw [map_mul, hu, hv, _root_.mul_one]) 1 1
  rw [map_mul, hadd u hu, hadd v hv, h1, h1, h1, _root_.mul_assoc, _root_.mul_assoc, mul_right_inj,
    ← _root_.mul_assoc, ← _root_.mul_assoc, mul_left_inj] at h
  exact h

include hmm h1 hadd in

theorem comb_comb {m n : ℕ} (v : Fin m → Γ) (hv : ∀ i, sm 0 (v i) = 1) (M : Fin n → Fin m → R) (b : Fin n → R) :
    (List.ofFn fun j => sm (b j) (List.ofFn fun i => sm (M j i) (v i)).prod).prod =
      (List.ofFn fun i => sm (∑ j, b j * M j i) (v i)).prod := by
  classical
  let K := (sm 0).ker
  let _ : CommGroup K := { (inferInstance : Group K) with
    mul_comm := fun x y => Subtype.ext (commute_of_scalars sm h1 hadd x.2 y.2) }
  let s : R → K →* K := fun a => ((sm a).comp K.subtype).codRestrict K fun x => by
    have hx : sm 0 x = 1 := x.2
    show sm 0 (sm a x) = 1
    rw [hmm, zero_mul, hx]
  have hs : ∀ a (x : K), sm a x = K.subtype (s a x) := fun _ _ => rfl
  have hp : ∀ {k : ℕ} (f : Fin k → K), (List.ofFn fun i => K.subtype (f i)).prod = K.subtype (∏ i, f i) := fun f => by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]; rfl
  have hsum : ∀ (x : K) (t : Finset (Fin n)) (a : Fin n → R), s (∑ j ∈ t, a j) x = ∏ j ∈ t, s (a j) x := by
    intro x t a
    induction t using Finset.induction_on with
    | empty => exact Subtype.ext x.2
    | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, ← ih]
      exact Subtype.ext (hadd x x.2 _ _)
  have hss : ∀ a b (x : K), s a (s b x) = s (a * b) x := fun a b x => Subtype.ext (hmm a b x)
  obtain ⟨w, rfl⟩ : ∃ w : Fin m → K, v = fun i => (w i : Γ) := ⟨fun i => ⟨v i, hv i⟩, rfl⟩
  have e : ∀ j, sm (b j) (List.ofFn fun i => sm (M j i) (w i : Γ)).prod = K.subtype (s (b j) (∏ i, s (M j i) (w i))) :=
    fun j => congrArg (sm (b j)) (hp fun i => s (M j i) (w i))
  rw [funext e, hp]
  refine Eq.trans (congrArg K.subtype ?_) (hp fun i => s (∑ j, b j * M j i) (w i)).symm
  simp only [map_prod, hss, hsum]
  exact Finset.prod_comm

end Abstract

section General

variable {V R : Type} [CommRing V] [CommRing R] [Algebra V R] {G : Over (Sp V)} [GrpObj G]

def epsHom (V : Type) {R : Type} [CommRing V] [CommRing R] [Algebra V R] (a : R) : epsOver V R ⟶ epsOver V R :=
  Over.homMk (spMap (epsMul a)) (by
    show spMap (epsMul a) ≫ spMap _ = spMap _
    rw [Formalism.L2.PjFree.spMap_comp', ← RingHom.comp_assoc, Formalism.L2.PjFree.epsMul_comp_alg])

def epsScal (G : Over (Sp V)) [GrpObj G] (a : R) : (epsOver V R ⟶ G) →* (epsOver V R ⟶ G) where
  toFun v := epsHom V a ≫ v
  map_one' := MonObj.comp_one _
  map_mul' := MonObj.comp_mul _

theorem isComb_iff {m : ℕ} (v : Fin m → (epsOver V R ⟶ G)) (cf : Fin m → R) (w : epsOver V R ⟶ G) :
    IsComb v cf w ↔ w = (List.ofFn fun i => epsScal G (cf i) (v i)).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [show u = fun i => epsScal G (cf i) (v i) from funext fun i => Over.OverMorphism.ext (hu i)]
  · rintro rfl
    exact ⟨_, fun _ => rfl, rfl⟩

theorem isTan_iff (v : epsOver V R ⟶ G) : IsTan v ↔ epsScal G 0 v = 1 := by
  have he : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
  let p : epsOver V R ⟶ ptOver V R := Over.homMk (spMap (algebraMap R (DualNumber R)))
    (Formalism.L2.PjFree.spMap_comp' _ _)
  let q : ptOver V R ⟶ epsOver V R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    show spMap _ ≫ spMap _ = spMap _
    rw [Formalism.L2.PjFree.spMap_comp', ← RingHom.comp_assoc, hid, RingHom.id_comp])
  have hpq : epsHom V (0 : R) = p ≫ q := Over.OverMorphism.ext (by
    show spMap _ = spMap _ ≫ spMap _
    rw [Formalism.L2.PjFree.spMap_comp', he])
  have hqp : q ≫ p = 𝟙 _ := Over.OverMorphism.ext (by
    show spMap _ ≫ spMap _ = 𝟙 _
    rw [Formalism.L2.PjFree.spMap_comp', hid]
    exact Spec.map_id _)
  constructor
  · intro h
    have h' : q ≫ v = 1 := Over.OverMorphism.ext h
    show epsHom V 0 ≫ v = 1
    rw [hpq, Category.assoc, h', MonObj.comp_one]
  · intro h
    have h' : q ≫ epsHom V 0 ≫ v = q ≫ 1 := congrArg (q ≫ ·) h
    rw [hpq, Category.assoc, ← Category.assoc q p, hqp, Category.id_comp, MonObj.comp_one] at h'
    exact congrArg (·.left) h'

theorem epsScal_epsScal (a b : R) (v : epsOver V R ⟶ G) : epsScal G a (epsScal G b v) = epsScal G (a * b) v := by
  apply Over.OverMorphism.ext
  show spMap (epsMul a) ≫ spMap (epsMul b) ≫ v.left = spMap (epsMul (a * b)) ≫ v.left
  rw [← Category.assoc, Formalism.L2.PjFree.spMap_comp']
  congr 2
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, _root_.mul_assoc]

theorem epsScal_one (v : epsOver V R ⟶ G) : epsScal G 1 v = v := by
  apply Over.OverMorphism.ext
  show spMap (epsMul (1 : R)) ≫ v.left = v.left
  have he : epsMul (1 : R) = RingHom.id _ := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul]
  rw [he]
  exact (congrArg (· ≫ v.left) (Spec.map_id _)).trans (Category.id_comp _)

theorem epsScal_add (v : epsOver V R ⟶ G) (h0 : epsScal G 0 v = 1) (a b : R) :
    epsScal G (a + b) v = epsScal G a v * epsScal G b v := by
  obtain ⟨φ, hφ⟩ : ∃ φ : overAt (spMap (algebraMap V R)) (DualNumber R) ⟶ epsOver V R,
      φ.left = 𝟙 (Sp (DualNumber R)) :=
    ⟨Over.homMk (𝟙 (Sp (DualNumber R))) ((Category.id_comp _).trans
      (Formalism.L2.PjFree.spMap_comp' (algebraMap V R) (algebraMap R (DualNumber R))).symm), rfl⟩
  have hl : ∀ u : epsOver V R ⟶ G, (φ ≫ u).left = u.left := fun u => by
    rw [Over.comp_left, hφ]; exact Category.id_comp _
  have hs : ∀ a : R, GlobalTheory.FrameTangent.smT (spMap (algebraMap V R)) a (φ ≫ v) = φ ≫ epsScal G a v :=
    fun a => Over.OverMorphism.ext (by rw [GlobalTheory.FrameTangent.smT_left, hl, hl]; rfl)
  have h := GlobalTheory.FrameTangent.smT_add (spMap (algebraMap V R)) (φ ≫ v)
    (by rw [hs, h0, MonObj.comp_one]) a b
  rw [hs, hs, hs, ← MonObj.comp_mul] at h
  apply Over.OverMorphism.ext
  rw [← hl, h, hl]

theorem combLinear : CombLinear := by
  intro V R _ _ _ G _ m v hv
  replace hv : ∀ i, epsScal G 0 (v i) = 1 := fun i => (isTan_iff _).1 (hv i)
  refine ⟨fun cf => ⟨_, (isComb_iff _ _ _).2 rfl, fun _ h => (isComb_iff _ _ _).1 h⟩, fun cf w hw => ?_, fun i => ?_,
    fun n M w hw b z hz => ?_⟩
  · rw [isTan_iff, (isComb_iff _ _ _).1 hw, map_list_prod, List.map_ofFn]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact (epsScal_epsScal _ _ _).trans (by rw [zero_mul, hv])
  · rw [isComb_iff, List.ofFn_eq_map, List.prod_map_eq_pow_single i _ fun j hj _ => by
      rw [Pi.single_eq_of_ne hj, hv], List.count_eq_one_of_mem (List.nodup_finRange m) (List.mem_finRange i),
      pow_one, Pi.single_eq_same, epsScal_one]
  · rw [isComb_iff, (isComb_iff _ _ _).1 hz, funext fun j => (isComb_iff _ _ _).1 (hw j)]
    exact comb_comb (epsScal G) epsScal_epsScal epsScal_one epsScal_add v hv M b

end General

section Pull

variable {X S : Scheme.{0}} (x : S ⟶ X) (G : Over X) [GrpObj G]

attribute [local instance] Functor.grpObjObj

theorem exists_pullHom (T : Over X) (T₀ : Over S) (e : T₀.left ⟶ T.left) (he : e ≫ T.hom = T₀.hom ≫ x) :
    ∃ Φ : (T ⟶ G) →* (T₀ ⟶ (Over.pullback x).obj G), ∀ u, (Φ u).left ≫ pullback.fst G.hom x = e ≫ u.left := by
  let ψ : T₀ ⟶ (Over.pullback x).obj T := Over.homMk (pullback.lift e T₀.hom he) (pullback.lift_snd _ _ _)
  refine ⟨{ toFun := fun u => ψ ≫ (Over.pullback x).map u
            map_one' := by rw [Functor.map_one, MonObj.comp_one]
            map_mul' := fun u w => by rw [Functor.map_mul, MonObj.comp_mul] }, fun u => ?_⟩
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, Over.comp_left, ψ, Over.homMk_left, Over.pullback_map_left]
  erw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem tanLin_of_combLinear (h : CombLinear) : TanLin Xo := by
  intro S _ x m v hv m' w A N w' hw hw'
  let _ : GrpObj ((Over.pullback x).obj Xo.univ.t.G) := Functor.grpObjObj
  obtain ⟨Φ, hΦ⟩ := exists_pullHom x Xo.univ.t.G (tEps x) (epsOver S S) (𝟙 (Sp (DualNumber S))) (Category.id_comp _)
  obtain ⟨Φ₀, hΦ₀⟩ := exists_pullHom x Xo.univ.t.G (Over.mk x) (ptOver S S) (𝟙 (Sp S))
    ((Category.id_comp _).trans ((congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp _)).symm)
  replace hΦ : ∀ u, (Φ u).left ≫ pullback.fst Xo.univ.t.G.hom x = u.left := fun u => (hΦ u).trans (Category.id_comp _)
  have ext : ∀ {T : Over (Sp S)} (a b : T ⟶ (Over.pullback x).obj Xo.univ.t.G),
      a.left ≫ pullback.fst Xo.univ.t.G.hom x = b.left ≫ pullback.fst Xo.univ.t.G.hom x → a = b := fun a b hab =>
    Over.OverMorphism.ext (pullback.hom_ext hab ((Over.w a).trans (Over.w b).symm))
  have key : ∀ {k : ℕ} (u : Fin k → (tEps x ⟶ Xo.univ.t.G)), (∀ j, IsTanAt x (u j).left) → ∀ (cf : Fin k → S)
      (z : tEps x ⟶ Xo.univ.t.G), IsComb (fun j => Φ (u j)) cf (Φ z) ↔ IsCombAt x (fun j => (u j).left) cf z.left := by
    intro k u hu cf z
    have e : ∀ j, epsScal _ (cf j) (Φ (u j)) = Φ (Formalism.L2.PjFree.epsPt (hu j) (cf j)) := fun j => ext _ _ (by
      rw [hΦ, Formalism.L2.PjFree.epsPt_left, ← hΦ (u j), ← Category.assoc]
      rfl)
    have e' : (List.ofFn fun j => epsScal _ (cf j) (Φ (u j))).prod =
        Φ (List.ofFn fun j => Formalism.L2.PjFree.epsPt (hu j) (cf j)).prod := by
      rw [map_list_prod, List.map_ofFn, funext e]
      rfl
    have hc := Formalism.L2.PjFree.isCombAt_epsPt hu cf
    rw [isComb_iff, e']
    constructor
    · intro hz
      rw [← hΦ z, hz, hΦ]
      exact hc
    · intro hz
      exact congrArg Φ (Over.OverMorphism.ext (Formalism.L2.PjFree.isCombAt_unique hz hc))
  have tw : ∀ i, IsTanAt x (w i) := fun i => isTanAt_of_isCombAt hv (hw i)
  let v₁ : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk (v j) (hv j).1
  let w₁ : Fin m' → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk (w j) (tw j).1
  let z₁ : tEps x ⟶ Xo.univ.t.G := Over.homMk w' (isTanAt_of_isCombAt tw hw').1
  have ht : ∀ j, IsTan (Φ (v₁ j)) := fun j => by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hΦ, ← map_one Φ₀, hΦ₀]
      exact (hv j).2.trans (Category.id_comp _).symm
    · refine Eq.trans ?_ (Over.w (1 : ptOver S S ⟶ (Over.pullback x).obj Xo.univ.t.G)).symm
      refine (Category.assoc _ _ _).trans ((congrArg _ (Over.w (Φ (v₁ j)))).trans ?_)
      refine (Formalism.L2.PjFree.spMap_comp' _ _).trans (congrArg spMap ?_)
      ext r
      simp [TrivSqZeroExt.algebraMap_eq_inl]
  have := (key v₁ hv _ z₁).1 ((h S S _ m _ ht).2.2.2 m' (fun i j => A j i) _
    (fun i => (key v₁ hv _ (w₁ i)).2 (hw i)) N _ ((key w₁ tw _ z₁).2 hw'))
  rwa [show (fun j => ∑ i, N i * A j i) = A.mulVec N from funext fun j => Finset.sum_congr rfl fun i _ => mul_comm _ _]
    at this

theorem spread : SpreadSt Xo c :=
  GlobalTheory.Frames.framedPoint_field_fromTest GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c

theorem reFrame_iff_integral : ReFrame Xo c ↔ ReframeIntegral Xo c :=
  reFrame_iff_reframeIntegral Xo c (spread Xo c)

theorem intLieGL_iff_intFr : IntLieGL Xo c ↔ IntFrLieGL Xo c := intLieGL_iff Xo c (spread Xo c)

theorem genRatio : GenRatio Xo c :=
  fun _ _ _ y y' hx => ⟨genScal_existsUnique y y' hx, fun _ => isUnit_of_genScal⟩

theorem intFrameGL_iff : IntFrameGL Xo c ↔ IntDiagUnit Xo c := by
  have hS := spread Xo c
  refine ⟨intDiagUnit_of_intFrameGL, fun hU => ?_⟩
  have hL : IntLieGL Xo c := (intLieGL_iff_intFr Xo c).2 (intFrLieGL_of
    (fun S _ x _ v hv _ w A N w' hw hw' => GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw')
    (GlobalTheory.IntRebase.intRebase_of hS) hU)
  refine ⟨hL, fun T io => ?_⟩
  let _ := io.toAlgebra
  intro y y' hy hy' hx
  choose M hM using hL T io y y' hy hy' hx
  have hk' : ∀ τ, IsUnit (M τ).1.transpose.det := fun τ => by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 (M τ).isUnit
  have hK : ∀ τ, IsUnit ((M τ).1.transpose.map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((M τ).1.transpose.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (M τ).1.transpose.det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk' τ).map _
  have hr := GlobalTheory.IntRebase.integral_reb T io y hy (fun τ => (M τ).1.transpose) hk' hK
  have eu : y'.u = (GlobalTheory.IntRebase.rebase₂ y _ hK).u := by
    funext τ i
    exact Formalism.L2.PjFree.isCombAt_unique (hM τ i)
      ((GlobalTheory.IntRebase.isCombAtG_iff Xo.univ.t y.x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (y.tan τ j)) _ _).2 rfl)
  obtain ⟨a, ha, -⟩ := genScal_existsUnique y y' hx
  have hu := isUnit_of_genScal ha
  have hb : FrBor (fun o : Ix Dw => o.elim hu.unit fun _ => 1) (GlobalTheory.IntRebase.rebase₂ y _ hK) y' := by
    refine ⟨hx, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩, ?_⟩
    · rw [eu]; exact Formalism.L2.PjFree.isCombAt_single ((GlobalTheory.IntRebase.rebase₂ y _ hK).tan τ) i
    · exact (sClause_iff a (GlobalTheory.IntRebase.rebase₂ y _ hK) y').2 ha
  have hv : valV T.V a = 1 := hU T io ⟨_, hS _ _, hr⟩ ⟨y', hS _ _, hy'⟩ _ hb none
  obtain ⟨a₀, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) hv.le
  have : IsUnit a₀ := IsLocalRing.notMem_maximalIdeal.1
    (((IsDiscreteValuationRing.maximalIdeal T.V).valuation_eq_one_iff_notMem).1 hv)
  exact ⟨this.unit, ha⟩

theorem xoNumPt_iff_framed : XoNumPt Xo c ↔ FramedPointNumberField Xo c := by
  classical
  rw [xoNumPt_iff]
  refine ⟨?_, pointNumberField_of_framed⟩
  rintro ⟨L, _, _, hL, x, hx⟩
  obtain ⟨y, -⟩ := gfp_frPt_gen (L' := L) GlobalTheory.abelianSchemeLaws_all.2.secTwist (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  exact ⟨L, inferInstance, inferInstance, hL, ⟨y⟩⟩

theorem claims_iff : Claims Xo c ↔
    FrBaseChg Xo c ∧ ReFrame Xo c ∧ XoNumPt Xo c ∧ TanLin Xo ∧ IntDiagUnit Xo c ∧ CombLinear := by
  have h1 := frBaseChg_iff Xo c
  have h2 := reFrame_iff Xo c
  have h3 := reFrame_iff_integral Xo c
  have h4 := xoNumPt_iff Xo c
  have h5 := xoNumPt_iff_framed Xo c
  have h6 := tanLin_iff Xo c
  have h7 := intFrameGL_iff Xo c
  have h8 := genRatio Xo c
  unfold Claims
  tauto

theorem reframe_compare :
    (FrBaseChg Xo c ↔ BaseChangeField Xo c) ∧ (ReFrame Xo c ↔ ReframeIntFr Xo c) ∧
      (ReFrame Xo c ↔ ReframeIntegral Xo c) ∧ (XoNumPt Xo c ↔ PointNumberField Xo c) ∧
      (TanLin Xo ↔ CombLinearAt Xo c) ∧
      (∀ (S : Type) [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S), SClause a y y' ↔ GenScal a y y') ∧
      (IntRebase Xo c ↔ LieRebase Xo c) ∧ (IntFrameGL Xo c ↔ IntDiagUnit Xo c) ∧ GenRatio Xo c ∧
      (XoNumPt Xo c ↔ FramedPointNumberField Xo c) ∧ (CombLinear → TanLin Xo) ∧ CombLinear ∧
      (Claims Xo c ↔ FrBaseChg Xo c ∧ ReFrame Xo c ∧ XoNumPt Xo c ∧ TanLin Xo ∧ IntDiagUnit Xo c ∧ CombLinear) ∧
      (Claims Xo c ↔ FrBaseChg Xo c ∧ ReFrame Xo c ∧ XoNumPt Xo c ∧ TanLin Xo ∧ IntDiagUnit Xo c) :=
  ⟨frBaseChg_iff Xo c, reFrame_iff Xo c, reFrame_iff_integral Xo c, xoNumPt_iff Xo c, tanLin_iff Xo c,
    fun _ _ _ => sClause_iff, intRebase_iff Xo c, intFrameGL_iff Xo c, genRatio Xo c, xoNumPt_iff_framed Xo c,
    tanLin_of_combLinear Xo, combLinear, claims_iff Xo c, by simp only [claims_iff, combLinear, and_true]⟩

end GlobalTheory.ReframeCompare
