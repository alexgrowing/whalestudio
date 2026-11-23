import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecRel

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart scaleD)
open Formalism.L2.Pj.GSR (Rel viaT liftT)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

instance gsvActHom (a : 𝓞 E) : IsMonHom (Xo.univ.t.act.act a) := Xo.univ.t.act.hom a

theorem gsv_hcId : IsGrpPullback Xo.univ.t.G Xo.univ.t.G (𝟙 Xo.X) (𝟙 Xo.univ.t.G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  let e : Over.mk (T.hom ≫ 𝟙 Xo.X) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have h1 : x₀ = e ≫ x := by
    apply Over.OverMorphism.ext
    simpa [e] using hx
  have h2 : y₀ = e ≫ y := by
    apply Over.OverMorphism.ext
    simpa [e] using hy
  subst h1 h2
  rw [← comp_mul]
  simp [e]

def gsvVec {L : Type} [CommRing L] (x : Sp L ⟶ Xo.X) {n : ℕ}
    (xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G)
    (cc : Fin n → L) : Sp (DualNumber L) ⟶ Xo.univ.t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x

section V

variable {L : Type} [CommRing L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem gsvVec_w (cc : Fin n → L) :
    gsvVec x xc cc ≫ Xo.univ.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ x := by
  have h1 := Over.w (tvec (x := xc) cc)
  rw [gsvVec, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) h1

variable (xc) in

def gsvW (cc : Fin n → L) : tEps x ⟶ Xo.univ.t.G := Over.homMk (gsvVec x xc cc) (gsvVec_w cc)

variable (xc) in
theorem gsv_rel (cc : Fin n → L) :
    Rel (F := 𝟙 Xo.univ.t.G.left) x x
      (gsvW xc cc : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) (tvec (x := xc) cc) := by
  show (gsvW xc cc).left ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

theorem gsv_tan (hx : IsUnivChart _ n xc) (cc : Fin n → L) : IsTanAt x (gsvVec x xc cc) := by
  refine ⟨gsvVec_w cc, ?_⟩
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  have ht : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ tvec (x := xc) cc = 1 :=
    ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc
  have hr := Formalism.L2.Pj.GSR.rel_pre
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) (gsv_rel xc cc)
  rw [ht] at hr
  have h1 : Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫
      gsvW xc cc = 1 := by
    first
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hc htk hr (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hc hr (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_w hr (Formalism.L2.Pj.GSR.rel_one hc htk)
  calc spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ gsvVec x xc cc
      = (Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫
          gsvW xc cc).left := rfl
    _ = (1 : _ ⟶ Xo.univ.t.G).left := congrArg Over.Hom.left h1
    _ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
      let e : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) ⟶ Over.mk x :=
        Over.homMk (𝟙 _) (by simp [ReciprocityTheory.ChartRestriction.G.Chart.sp])
      rw [← comp_one e]
      simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]
      try rfl

theorem gsv_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) :
    ∃ cc, w = gsvVec x xc cc := by
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let W : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G := Over.homMk w hw.1
  obtain ⟨v, hv⟩ : ∃ v, Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x W v := by
    first
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc htk W
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc htk
    | exact Formalism.L2.Pj.GSR.rel_exists_v hc W
    | exact Formalism.L2.Pj.GSR.rel_exists_v W
  have hone : Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) ≫ W = 1 := by
    apply Over.OverMorphism.ext
    let e : viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) L) ⟶ Over.mk x :=
      Over.homMk (𝟙 _) (by simp [ReciprocityTheory.ChartRestriction.G.Chart.sp])
    rw [← comp_one e]
    simp only [e, W, Formalism.L2.Pj.GSR.liftT, Over.comp_left, Over.homMk_left, Category.id_comp]
    exact hw.2
  have hv1 := Formalism.L2.Pj.GSR.rel_pre (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L)) hv
  rw [hone] at hv1
  have htan : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD L) ≫ v = 1 := by
    first
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hc htk hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hc hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
    | exact Formalism.L2.Pj.GSR.rel_uniq_v hv1 (Formalism.L2.Pj.GSR.rel_one hc htk)
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v htan, ?_⟩
  have hs := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v htan
  have hv' : w ≫ 𝟙 _ = v.left ≫ pullback.fst Xo.univ.t.G.hom x := hv
  rw [Category.comp_id] at hv'
  rw [hv']
  exact congrArg (fun f => f.left ≫ pullback.fst Xo.univ.t.G.hom x) hs

theorem gsv_inj (hx : IsUnivChart _ n xc) {c₁ c₂ : Fin n → L} (h : gsvVec x xc c₁ = gsvVec x xc c₂) : c₁ = c₂ := by
  have ht : tvec (x := xc) c₁ = tvec (x := xc) c₂ := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact h
    · exact (Over.w (tvec (x := xc) c₁)).trans (Over.w (tvec (x := xc) c₂)).symm
  first
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj ht
  | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx ht

theorem gsv_eig_iff [Algebra c.F L] (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) (cc : Fin n → L) :
    IsEigAt c τ (gsvVec x xc cc) ↔
      cc ∈ eigLat hx (fun a => (Over.pullback x).map (Xo.univ.t.act.act a)) (fun a => algebraMap c.F L (embK c τ a)) := by
  have e1 : ∀ a : 𝓞 E, ((Over.pullback x).map (Xo.univ.t.act.act a)).left ≫ pullback.fst Xo.univ.t.G.hom x =
      pullback.fst Xo.univ.t.G.hom x ≫ (Xo.univ.t.act.act a).left := by
    intro a
    simp
    first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]
    | (rw [limit.lift_π]; rfl)
  have key : ∀ a : 𝓞 E, (gsvVec x xc cc ≫ (Xo.univ.t.act.act a).left =
      spMap (epsMul (algebraMap c.F L (embK c τ a))) ≫ gsvVec x xc cc) ↔
      (tvec (x := xc) cc ≫ (Over.pullback x).map (Xo.univ.t.act.act a) =
        ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (algebraMap c.F L (embK c τ a))) ≫ tvec (x := xc) cc) := by
    intro a
    constructor
    · intro h
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · simp only [Over.comp_left, Category.assoc, e1]
        simp only [gsvVec] at h
        rw [← Category.assoc, h]
        rfl
      · exact (Over.w _).trans (Over.w _).symm
    · intro h
      have h' := congrArg (fun f => f.left ≫ pullback.fst Xo.univ.t.G.hom x) h
      simp only [Over.comp_left, Category.assoc, e1] at h'
      simp only [gsvVec, Category.assoc]
      exact h'
  simp only [IsEigAt, key, eigLat, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff ..

theorem gsv_tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → L) (e : Fin m → Fin n → L) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  induction m with
  | zero =>
    simp only [Fin.sum_univ_zero, List.ofFn_zero, List.prod_nil]
    have h := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → L) 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx,
      List.ofFn_succ, List.prod_cons, ih (fun j => a j.succ) (fun j => e j.succ)]

theorem gsv_comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → L) (a : Fin m → L) (cc : Fin n → L) :
    IsCombAt x (fun j => gsvVec x xc (e j)) a (gsvVec x xc cc) ↔ cc = ∑ j, a j • e j := by
  have hc := gsv_hcId (Xo := Xo)
  have htk : x ≫ 𝟙 Xo.X = x := Category.comp_id x
  let u0 : Fin m → (viaT x (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (DualNumber L)) ⟶ Xo.univ.t.G) := fun j =>
    Formalism.L2.Pj.GSR.liftT x (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j))) ≫ gsvW xc (e j)
  have hrel : ∀ j, Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x (u0 j)
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)) :=
    fun j => Formalism.L2.Pj.GSR.rel_pre _ (gsv_rel xc (e j))
  have hprod : Formalism.L2.Pj.GSR.Rel (F := 𝟙 Xo.univ.t.G.left) x x (List.ofFn u0).prod
      (tvec (x := xc) (∑ j, a j • e j)) := by
    rw [gsv_tvec_sum hx]
    first
    | exact Formalism.L2.Pj.GSR.rel_prod hc htk u0 _ hrel
    | exact Formalism.L2.Pj.GSR.rel_prod hc u0 _ hrel
    | exact Formalism.L2.Pj.GSR.rel_prod u0 _ hrel
  have hleft : ((List.ofFn u0).prod).left = gsvVec x xc (∑ j, a j • e j) := by
    have h : ((List.ofFn u0).prod).left ≫ 𝟙 _ =
        (tvec (x := xc) (∑ j, a j • e j)).left ≫ pullback.fst Xo.univ.t.G.hom x := hprod
    rw [Category.comp_id] at h
    exact h
  constructor
  · rintro ⟨u, hu, hprodu⟩
    have hue : u = u0 := by
      funext j
      apply Over.OverMorphism.ext
      rw [hu j]
      rfl
    subst hue
    exact gsv_inj hx (hprodu.symm.trans hleft)
  · intro h
    subst h
    exact ⟨u0, fun j => rfl, hleft⟩

end V

end Formalism.L2.Pj
