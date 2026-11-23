import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj.LieRel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tcoord tmap IsUnivChart tvec_tmap tcoord_spec tvec_inj list_prod_tan' tcoord_scale
  tcoord_tvec isTan_tvec isTan_scale tvec_eig_iff scaleD fB Rel liftT viaT rel_exists_w rel_exists_v rel_eq_iff
  rel_prod rel_pre tan_iff eig_iff one_left' sp JetR)

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Vside

variable {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := V) (JetR V (Fin n) m) ⟶ G} (hx : IsUnivChart G n xc)

theorem epsOver_hom : (epsOver V V).hom = (sp (R₀ := V) (DualNumber V)).hom := rfl

def eV : epsOver V V ⟶ sp (R₀ := V) (DualNumber V) :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans epsOver_hom.symm)

def cvV (y : sp (R₀ := V) (DualNumber V) ⟶ G) : epsOver V V ⟶ G := eV ≫ y

theorem cvV_left (y : sp (R₀ := V) (DualNumber V) ⟶ G) : (cvV y).left = y.left := by
  simp [cvV, eV]

theorem cvV_inj {y y' : sp (R₀ := V) (DualNumber V) ⟶ G} (h : cvV y = cvV y') : y = y' :=
  Over.OverMorphism.ext (by rw [← cvV_left y, ← cvV_left y', h])

theorem cvV_prod {m : ℕ} (y : Fin m → (sp (R₀ := V) (DualNumber V) ⟶ G)) :
    (List.ofFn fun i => cvV (y i)).prod = cvV (List.ofFn y).prod := by
  show (List.ofFn fun i => preHom eV (y i)).prod = preHom eV (List.ofFn y).prod
  rw [map_list_prod, List.map_ofFn]
  rfl

theorem isTan_cvV {y : sp (R₀ := V) (DualNumber V) ⟶ G} (h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y) : IsTan (cvV y) := by
  have h' : ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD V) ≫ y = 1 := h
  have e : (ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD V) ≫ y).left =
      (1 : sp (R₀ := V) V ⟶ G).left := by rw [h']
  show spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ (cvV y).left = (1 : ptOver V V ⟶ G).left
  rw [cvV_left]
  exact e

include hx in
theorem tan_eq_cvV {w : epsOver V V ⟶ G} (h : IsTan w) : ∃ c : Fin n → V, w = cvV (tvec (x := xc) c) := by
  let y : sp (R₀ := V) (DualNumber V) ⟶ G := Over.homMk w.left ((Over.w w).trans epsOver_hom)
  have hy : ReciprocityTheory.ChartRestriction.G.Chart.IsTan y := Over.OverMorphism.ext h
  refine ⟨tcoord hx y hy, ?_⟩
  have e : y = tvec (x := xc) (tcoord hx y hy) := by
    first
    | exact tcoord_spec hx y hy
    | exact tcoord_spec y hy
  rw [← e]
  exact Over.OverMorphism.ext (by rw [cvV_left]; rfl)

theorem eigV_iff (e : G ⟶ G) [IsMonHom e] (c : Fin n → V) (z : V) :
    (cvV (tvec (x := xc) c) ≫ e).left = spMap (epsMul z) ≫ (cvV (tvec (x := xc) c)).left ↔ tmap hx e c = z • c := by
  have key : ∀ y : sp (R₀ := V) (DualNumber V) ⟶ G, (cvV y ≫ e).left = (y ≫ e).left := fun y => by
    rw [Over.comp_left, cvV_left, Over.comp_left]
  rw [key, cvV_left, ← tvec_eig_iff hx e c z]
  constructor
  · intro h
    exact Over.OverMorphism.ext h
  · intro h
    rw [h]
    rfl

include hx in
theorem prod_tvec {m : ℕ} (r : Fin m → V) (b : Fin m → Fin n → V) :
    (List.ofFn fun i => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (r i)) ≫ tvec (x := xc) (b i)).prod =
      tvec (x := xc) (∑ i, r i • b i) := by
  have h0 : tvec (x := xc) (0 : Fin n → V) = 1 := by
    have e := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → V) 0
    rw [add_zero] at e
    simpa using e.symm
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx]

include hx in
theorem comb_iff {m : ℕ} (b : Fin m → Fin n → V) (r : Fin m → V) (e : Fin n → V) :
    IsComb (fun i => cvV (tvec (x := xc) (b i))) r (cvV (tvec (x := xc) e)) ↔ e = ∑ i, r i • b i := by
  have hprod : (List.ofFn fun i => cvV (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (r i)) ≫ tvec (x := xc) (b i))).prod =
      cvV (tvec (x := xc) (∑ i, r i • b i)) := by
    rw [cvV_prod, prod_tvec hx]
  constructor
  · rintro ⟨u, hu1, hw⟩
    have hu' : u = fun i => cvV (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (r i)) ≫ tvec (x := xc) (b i)) :=
      funext fun i => Over.OverMorphism.ext (by rw [hu1, cvV_left, cvV_left] <;> rfl)
    rw [hu', hprod] at hw
    first
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (cvV_inj hw)
    | exact ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj (cvV_inj hw)
  · intro he
    refine ⟨fun i => cvV (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (r i)) ≫ tvec (x := xc) (b i)), fun i => ?_, ?_⟩
    · rw [cvV_left, cvV_left] <;> rfl
    · rw [hprod, he]

end Vside

section Kside

variable {K : Type} [Field K] {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : Sp K ⟶ S) {G' : Over (Sp K)} [GrpObj G']
  {F1 : G'.left ⟶ A.left} (h1 : IsGrpPullback G' A x F1) {V : Type} [CommRing V] [Algebra V K] {G : Over (Sp V)}
  [GrpObj G] {F2 : G'.left ⟶ G.left} (h2 : IsGrpPullback G' G (fB V K) F2)

abbrev epsAt : Over S := Over.mk (spMap (algebraMap K (DualNumber K)) ≫ x)

theorem epsMul_alg (s : K) :
    spMap (epsMul s) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun a => by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_alg : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hid : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K :=
    RingHom.ext fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hid, CommRingCat.ofHom_id, Spec.map_id]

def iotaX : epsAt x ⟶ Over.mk ((viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K))).hom ≫ x) :=
  Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ ((sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _) ≫ x = spMap (algebraMap K (DualNumber K)) ≫ x
    rw [Category.id_comp, Category.comp_id]; rfl)

def phiX : (viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G') →* (epsAt x ⟶ A) :=
  (preHom (iotaX x)).comp (pushHom h1 _)

theorem phiX_left (w : viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G') : (phiX x h1 w).left = w.left ≫ F1 := by
  show (iotaX x ≫ pushPt h1.1.w w).left = w.left ≫ F1
  simp [iotaX, pushPt]

def RelA (F1 : G'.left ⟶ A.left) (F2 : G'.left ⟶ G.left) (v : epsAt x ⟶ A)
    (y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G) : Prop :=
  ∃ w : viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G', Rel (F := F2) (𝟙 _) (fB V K) w y ∧ v.left = w.left ≫ F1

include h1 h2 in
theorem relA_exists_v (y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G) :
    ∃ v : epsAt x ⟶ A, RelA x F1 F2 v y := by
  obtain ⟨w, hw⟩ := rel_exists_w h2 (Category.id_comp _) y
  exact ⟨phiX x h1 w, w, hw, phiX_left x h1 w⟩

include h1 h2 in
theorem relA_exists_y (v : epsAt x ⟶ A) :
    ∃ y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G, RelA x F1 F2 v y := by
  obtain ⟨w, hw⟩ : ∃ w : viaT (𝟙 (Sp K)) (sp (R₀ := K) (DualNumber K)) ⟶ G', v.left = w.left ≫ F1 :=
    ⟨Over.homMk (h1.1.lift v.left (spMap (algebraMap K (DualNumber K))) (by simpa using Over.w v)) (by simp),
      (h1.1.lift_fst _ _ _).symm⟩
  obtain ⟨y, hy⟩ := rel_exists_v h2 (Category.id_comp _) w
  exact ⟨y, w, hy, hw⟩

include h1 h2 in
theorem relA_uniq {v v' : epsAt x ⟶ A} {y y' : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) (h' : RelA x F1 F2 v' y') : v = v' ↔ y = y' := by
  obtain ⟨w, hwy, hwv⟩ := h
  obtain ⟨w', hwy', hwv'⟩ := h'
  rw [← rel_eq_iff h2 hwy hwy']
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (h1.1.hom_ext (hwv.symm.trans hwv') (by rw [Over.w w, Over.w w']))
  · rintro rfl
    exact Over.OverMorphism.ext (by rw [hwv, hwv'])

include h1 h2 in
theorem relA_prod {N : ℕ} (v : Fin N → (epsAt x ⟶ A)) (y : Fin N → (sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G))
    (h : ∀ i, RelA x F1 F2 (v i) (y i)) : RelA x F1 F2 (List.ofFn v).prod (List.ofFn y).prod := by
  choose w hw hwv using h
  have hv : ∀ i, v i = phiX x h1 (w i) := fun i => Over.OverMorphism.ext (by rw [phiX_left, hwv])
  refine ⟨(List.ofFn w).prod, rel_prod h2 (Category.id_comp _) w y hw, ?_⟩
  rw [← phiX_left x h1, map_list_prod, List.map_ofFn]
  exact congrArg (fun l => (List.prod l).left) (congrArg List.ofFn (funext hv))

def sclA (s : K) : epsAt x ⟶ epsAt x := Over.homMk (spMap (epsMul s)) (by
  show spMap (epsMul s) ≫ spMap (algebraMap K (DualNumber K)) ≫ x = spMap (algebraMap K (DualNumber K)) ≫ x
  rw [← Category.assoc, epsMul_alg])

theorem relA_scl {v : epsAt x ⟶ A} {y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) (s : K) :
    RelA x F1 F2 (sclA x s ≫ v) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s) ≫ y) := by
  obtain ⟨w, hwy, hwv⟩ := h
  refine ⟨liftT (𝟙 (Sp K)) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s)) ≫ w, rel_pre _ hwy, ?_⟩
  show spMap (epsMul s) ≫ v.left = ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s)).left ≫ w.left) ≫ F1
  rw [Category.assoc, ← hwv]
  rfl

include h1 h2 in
theorem relA_tan {v : epsAt x ⟶ A} {y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan y := by
  have hb : (1 : Over.mk (𝟙 (Sp K)) ⟶ G').left ≫ F1 = (1 : Over.mk x ⟶ A).left := by
    have e : (pushHom h1 (Over.mk (𝟙 (Sp K))) 1).left =
        (1 : Over.mk ((Over.mk (𝟙 (Sp K))).hom ≫ x) ⟶ A).left := by
      rw [map_one]
    change (1 : Over.mk (𝟙 (Sp K)) ⟶ G').left ≫ F1 = _ at e
    rw [e, one_left', one_left']
    simp
  obtain ⟨w, hwy, hwv⟩ := h
  rw [← tan_iff h2 (Category.id_comp _) hwy, hwv, ← hb]
  constructor
  · intro e
    apply h1.1.hom_ext
    · rw [Category.assoc]
      exact e
    · rw [Category.assoc, Over.w w, Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ G')]
      simpa using fst_alg
  · intro e
    rw [← Category.assoc, e]

include h1 h2 in
theorem relA_eig {v : epsAt x ⟶ A} {y : sp (R₀ := K) (DualNumber K) ⟶ (Over.pullback (fB V K)).obj G}
    (h : RelA x F1 F2 v y) (a : G' ⟶ G') (aA : A ⟶ A) (b : G ⟶ G) (h1a : a.left ≫ F1 = F1 ≫ aA.left)
    (h2a : a.left ≫ F2 = F2 ≫ b.left) (s : K) :
    v.left ≫ aA.left = spMap (epsMul s) ≫ v.left ↔
      y ≫ (Over.pullback (fB V K)).map b = ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD s) ≫ y := by
  obtain ⟨w, hwy, hwv⟩ := h
  rw [← eig_iff h2 a b h2a s hwy, hwv]
  constructor
  · intro e
    apply h1.1.hom_ext
    · simp only [Over.comp_left, Category.assoc, h1a]
      rw [Category.assoc] at e
      exact e
    · rw [Over.comp_left, Category.assoc, Over.w a, Category.assoc, Over.w w]
      show (sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _ =
        spMap (epsScale s) ≫ (sp (R₀ := K) (DualNumber K)).hom ≫ 𝟙 _
      simp only [Category.comp_id]
      exact (epsMul_alg s).symm
  · intro e
    rw [Category.assoc, ← h1a, ← Category.assoc, ← Over.comp_left, e, Category.assoc]
    rfl

end Kside

end Formalism.L2.Pj.LieRel
