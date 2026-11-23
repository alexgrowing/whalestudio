import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PsiUnitOnIffInterior
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DegActCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Type} [CommRing R] [IsDomain R]

section Act

variable {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem gtAct_iff (oa : D.OAct O) (a : O) (g g' : GtPtF D F) :
    GtAct oa a g g' ↔ TorusGraphMaps.GtSmul oa a g g' := by
  have hG := GlobalTheory.globalFns_holds
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  refine and_congr Iff.rfl ?_
  have vu : ∀ {f f' : D.P.A ⟶ D.P.A} (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f f') rosatiε))
      {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ x w : TF (R := R) F ⟶ D.P.A,
      val (LB.pullGen D.P.L _ _ u (lift x w).left) (𝟙 _) y J = val₂ u y J x w := fun u y J hJ x w => by
    rw [val_pull hJ, Category.id_comp]; rfl
  constructor
  · intro h
    have hr := oa.onB.rosati (star a)
    rw [star_star] at hr
    obtain ⟨u₁, h₁, n₁⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
    obtain ⟨u₂, h₂, n₂⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
    refine ⟨u₂, ⟨h₂, n₂⟩, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    have e := val_corr hJ (h u₁ h₁ n₁ χ) (𝟙 _)
    rw [val_mul hJ, vu u₁ hJ] at e
    rw [val_mul hJ, vu u₂ hJ, DVR.ros_swap hG D.P.isAb D.P.isLB _ _ u₁ h₁ n₁ u₂ h₂ n₂ hJ, ← e,
      mul_inv_cancel_right]
  · rintro ⟨u₂, ⟨h₂, n₂⟩, h⟩ u₁ h₁ n₁ χ
    refine corr_of_val D.P.isLB fun y J hJ => ?_
    have e := val_corr hJ (h χ) (𝟙 _)
    rw [val_mul hJ, vu u₂ hJ, DVR.ros_swap hG D.P.isAb D.P.isLB _ _ u₁ h₁ n₁ u₂ h₂ n₂ hJ] at e
    rw [val_mul hJ, vu u₁ hJ, ← e, inv_mul_cancel_right]

theorem qkAdd_iff {k : ℕ} (p p' p'' : QkPt D F k) :
    Geo.Tor.QkAdd p p' p'' ↔ TorusGraphMaps.QkAdd p p' p'' := Iff.rfl

theorem qkAct_iff (oa : D.OAct O) (a : O) {k : ℕ} (p p' : QkPt D F k) :
    QkAct oa a p p' ↔ TorusGraphMaps.QkSmul oa a p p' :=
  exists_congr fun q => and_congr Iff.rfl (and_congr (gtAct_iff oa a p.g q.g) Iff.rfl)

end Act

section Ext

variable {D : DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F']
  [Algebra (FractionRing R) F'] {k : ℕ}

theorem qkExt_iff (f : F →+* F') (p : QkPt D F k) (q : QkPt D F' k) :
    QkExt f p q ↔ ∃ σ : F →ₐ[FractionRing R] F', (σ : F →+* F') = f ∧ q.y = p.y ∧ TorusGraphMaps.GtMap σ p.g q.g := by
  constructor
  · intro h
    exact ⟨⟨f, fun r => DFunLike.congr_fun (DegActCheck.qkExt_compat f p q h) r⟩, rfl, h⟩
  · rintro ⟨σ, rfl, h⟩
    exact h

theorem qkMap_iff_exists (σ : F →ₐ[FractionRing R] F') (p : QkPt D F k) (p' : QkPt D F' k) :
    TorusGraphMaps.QkMap σ p p' ↔ ∃ q, QkExt (σ : F →+* F') p q ∧ QkPt.Equiv D F' q p' :=
  exists_congr fun _ => and_assoc.symm

theorem qkExt_unique {f : F →+* F'} {p : QkPt D F k} {q q' : QkPt D F' k} (h : QkExt f p q)
    (h' : QkExt f p q') : q = q' := by
  have hg : q.g = q'.g :=
    TorusExt.gt_ext_val (Over.OverMorphism.ext (h.2.1.trans h'.2.1.symm)) fun χ y J hJ =>
      (val_corr hJ (h.2.2 χ) _).trans (val_corr hJ (h'.2.2 χ) _).symm
  have hy : q.y = q'.y := h.1.trans h'.1.symm
  obtain ⟨y, g, e⟩ := q
  obtain ⟨y', g', e'⟩ := q'
  obtain rfl : y = y' := hy
  obtain rfl : g = g' := hg
  rfl

theorem forall_qkExt_iff (hB : D.TauBimult) (σ : F →ₐ[FractionRing R] F') (p : QkPt D F k) (p' : QkPt D F' k) :
    (∀ q, QkExt (σ : F →+* F') p q → QkPt.Equiv D F' q p') ↔ TorusGraphMaps.QkMap σ p p' := by
  rw [qkMap_iff_exists]
  constructor
  · intro h
    obtain ⟨q, hq, -⟩ := TorusExt.existsUnique_qkExt hB (σ : F →+* F') (RingHom.ext σ.commutes) p
    exact ⟨q, hq, h q hq⟩
  · rintro ⟨q, hq, e⟩ q' hq'
    rwa [qkExt_unique hq' hq]

end Ext

section Through

variable {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X]

abbrev rigVal (D : DegPre R) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r z J

abbrev rigB (D : DegPre R) :=
  LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom

theorem through_conditions (oa : D.OAct O) (w : O)
    (u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) (oa.onB.act w)).left, 𝟙 D.P.A.left, (oa.onB.act w).left,
        (toUnit D.P.A ≫ η[D.P.A]).left] ![1, -2, -1, 2]))
    (v : LB.Gen (LB.LinComb D.P.L (TorusGraphMaps.graphφ D.P.A (oa.onB.act w)) TorusGraphMaps.graphε))
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      val u r z J = val v r z J * rigVal D (r ≫ D.P.A.hom) z J) :
    (LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (eSec D.P.A)) (LB.oneGen D.P.L) ↔
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ v (eSec D.P.A)) (LB.invGen D.P.L _ _ D.rig)) ∧
    ∀ y, (LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (D.tau y (w • y)) (LB.pullGen D.P.L _ _ u (D.xK y)))
        (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK) ↔
      LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (D.tau y (w • y)) (LB.pullGen D.P.L _ _ v (D.xK y))) (D.psi y)) := by
  constructor
  · have e : ∀ z J, Good D.P.L z J → val (LB.pullGen D.P.L _ _ u (eSec D.P.A)) (𝟙 _) z J =
        val (LB.pullGen D.P.L _ _ v (eSec D.P.A)) (𝟙 _) z J *
          rigVal D (Z := (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (𝟙 _) z J := fun z J hJ => by
      have e₀ : (𝟙 _ ≫ eSec D.P.A) ≫ D.P.A.hom = 𝟙 _ := by
        rw [Category.id_comp]; exact Over.w η[D.P.A]
      rw [val_pull hJ, val_pull hJ, h _ _ z J hJ, e₀]
    constructor
    · intro c
      refine corr_of_val D.P.isLB fun z J hJ => ?_
      have a := (e z J hJ).symm.trans ((val_corr hJ c _).trans (val_one _))
      exact (eq_inv_of_mul_eq_one_left a).trans (val_inv _ _).symm
    · intro c
      refine corr_of_val D.P.isLB fun z J hJ => ?_
      have a := (val_corr hJ c (𝟙 _)).trans (val_inv _ _)
      exact (e z J hJ).trans (((congrArg (· * _) a).trans (inv_mul_cancel _)).trans (val_one _).symm)
  · intro y
    have e : ∀ z J, Good D.P.L z J →
        val (LB.mulGen D.P.L _ _ _ _ (D.tau y (w • y)) (LB.pullGen D.P.L _ _ u (D.xK y))) (𝟙 _) z J =
          val (LB.mulGen D.P.L _ _ _ _ (D.tau y (w • y)) (LB.pullGen D.P.L _ _ v (D.xK y))) (𝟙 _) z J *
            rigVal D (𝟙 _ ≫ (toUnit (TK R)).left) z J ∧
        val (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK) (𝟙 _) z J =
          val (D.psi y) (𝟙 _) z J * rigVal D (𝟙 _ ≫ (toUnit (TK R)).left) z J := fun z J hJ => by
      have e₀ : (𝟙 _ ≫ D.xK y) ≫ D.P.A.hom = 𝟙 _ ≫ (toUnit (TK R)).left := by
        rw [Category.id_comp, Category.id_comp]; exact Over.w (toUnit (TK R) ≫ D.c y)
      constructor
      · rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, h _ _ z J hJ, e₀, _root_.mul_assoc]
      · exact (val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))
    constructor
    · intro c
      refine corr_of_val D.P.isLB fun z J hJ => ?_
      exact mul_right_cancel ((e z J hJ).1.symm.trans ((val_corr hJ c _).trans (e z J hJ).2))
    · intro c
      refine corr_of_val D.P.isLB fun z J hJ => ?_
      exact (e z J hJ).1.trans ((congrArg (· * _) (val_corr hJ c _)).trans (e z J hJ).2.symm)

theorem prod_graph (f : D.P.A ⟶ D.P.A) {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ i, h (TorusGraphMaps.graphφ D.P.A f i) ^ TorusGraphMaps.graphε i =
      h (padd D.P.A (𝟙 _) f).left * (h (𝟙 _))⁻¹ * (h f.left)⁻¹ * h (toUnit D.P.A ≫ η[D.P.A]).left * (h (𝟙 _))⁻¹ := by
  rw [Fin.prod_univ_five]
  show h (padd D.P.A (𝟙 _) f).left ^ (1 : ℤ) * h (𝟙 _) ^ (-1 : ℤ) * h f.left ^ (-1 : ℤ) *
    h (toUnit D.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) * h (𝟙 _) ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_four (f : D.P.A ⟶ D.P.A) {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ i : Fin 4, h ((![(padd D.P.A (𝟙 _) f).left, 𝟙 D.P.A.left, f.left, (toUnit D.P.A ≫ η[D.P.A]).left] :
        Fin 4 → _) i) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) i =
      h (padd D.P.A (𝟙 _) f).left ^ (1 : ℤ) * h (𝟙 _) ^ (-2 : ℤ) * h f.left ^ (-1 : ℤ) *
        h (toUnit D.P.A ≫ η[D.P.A]).left ^ (2 : ℤ) := by
  rw [Fin.prod_univ_four]; rfl

theorem prod_rigB {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ _i : PUnit, h (D.P.A.hom ≫ eSec D.P.A) ^ (1 : ℤ) = h (toUnit D.P.A ≫ η[D.P.A]).left :=
  (Fintype.prod_unique _).trans (zpow_one _)

theorem psiW0_iff (oa : D.OAct O) (w : O) : TraceFormTwistIso D oa w ↔ TorusGraphMaps.PsiThrough oa w := by
  have hr : (rigB D).IsGen := DVR.pullGen_isGen _ _ _ _ D.rig_gen _
  constructor
  · rintro ⟨u, hu, n, hψ⟩
    obtain ⟨v, hv, e⟩ := exists_gen D.P.isLB (φ' := TorusGraphMaps.graphφ D.P.A (oa.onB.act w)) (ε' := TorusGraphMaps.graphε)
      (fun U _ h => by
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := PUnit) (U := U) _ (prod_four _ h)
          (DVR.prod_neg _ _ (prod_rigB h))).trans ?_
        rw [prod_graph]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        module)
      (LB.mulGen D.P.L _ _ _ _ u (LB.invGen D.P.L _ _ (rigB D)))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hr))
    have k := through_conditions oa w u v fun Z r z J hJ => by
      rw [e Z r z J hJ, val_mul hJ, val_inv, val_pull hJ, inv_mul_cancel_right]
    exact ⟨v, ⟨hv, k.1.1 n⟩, fun y => (k.2 y).1 (hψ y)⟩
  · rintro ⟨v, ⟨hv, n⟩, hψ⟩
    obtain ⟨u, hu, e⟩ := exists_gen D.P.isLB (K' := Fin 4)
      (φ' := ![(padd D.P.A (𝟙 _) (oa.onB.act w)).left, 𝟙 D.P.A.left, (oa.onB.act w).left,
        (toUnit D.P.A ≫ η[D.P.A]).left]) (ε' := ![1, -2, -1, 2])
      (fun U _ h => by
        refine (DVR.prod_sum₂ (K := Fin 5) (K' := PUnit) (U := U) _ (prod_graph _ h) (prod_rigB h)).trans ?_
        rw [prod_four]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
        module)
      (LB.mulGen D.P.L _ _ _ _ v (rigB D)) (DVR.mulGen_isGen _ _ _ _ _ _ _ hv hr)
    have k := through_conditions oa w u v fun Z r z J hJ => by
      rw [e Z r z J hJ, val_mul hJ, val_pull hJ]
    exact ⟨u, hu, k.1.2 n, fun y => (k.2 y).2 (hψ y)⟩

theorem psiW0_host_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {D : DegPre R}
    [Module (𝓞 E) D.X] (oa : letI := H.starRing; D.OAct (𝓞 E)) :
    (letI := H.starRing; TraceFormTwistIso D oa H.w0) ↔ TorusGraphMaps.PsiThroughHost H oa :=
  letI := H.starRing; psiW0_iff oa H.w0

end Through

section Unit

theorem jK_app_injective (W : (Spec (CommRingCat.of R)).Opens) : Function.Injective ((jK R).app W) := by
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  exact (jK R).app_injective W

variable (D : DegPre R) (χ : D.X)

theorem generic_le (j : PUnit → D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens}
    (hV : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hV hy

theorem psiGenOn_interior_of_psiUnitOn {U : Set (Spec (CommRingCat.of R))} (h : PsiUnitOn D χ U) :
    TorusGraphMaps.PsiGenOn D χ (interior U) := by
  intro x hx
  obtain ⟨i, hi⟩ := exists_chart D.P.isLB ((D.c χ).left x)
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Spec (CommRingCat.of R)) (x := x)
    (U := ⟨interior U, isOpen_interior⟩ ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U i) ⟨hx, hi⟩
  have h₂ : V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U i := fun y hy => (hle hy).2
  obtain ⟨r, hr, e⟩ := h (fun _ => i) V hV (fun y hy => interior_subset (hle hy).1) h₂ (generic_le D χ _ h₂)
  exact ⟨fun _ => i, V, hxV, h₂, generic_le D χ _ h₂, hr.unit, Units.ext e⟩

theorem psiUnitOn_of_psiGenOn {U : Set (Spec (CommRingCat.of R))} (h : TorusGraphMaps.PsiGenOn D χ U) :
    PsiUnitOn D χ U := by
  intro j V _ hU hj hh
  have loc : ∀ x : V, ∃ (W : (Spec (CommRingCat.of R)).Opens) (_ : W ≤ V) (_ : x.1 ∈ W)
      (u : Γ(Spec (CommRingCat.of R), W)ˣ), ∀ y, jK R y ∈ W →
        gm (jK R) y W u = gm (𝟙 (TK R).left) y (LB.wchart D.P.L (fun _ : PUnit => D.xK χ) j) ((D.psi χ).s j) := by
    intro x
    obtain ⟨j', V', hx, hj', h', r, e⟩ := h x.1 (hU x.2)
    have l : V ⊓ V' ≤ (D.c χ).left ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U (j' PUnit.unit)) :=
      fun y hy => ⟨hj hy.1, hj' hy.2⟩
    refine ⟨V ⊓ V', inf_le_left, ⟨x.2, hx⟩,
      (res l (pullU (D.c χ).left _ (D.P.L.g (j PUnit.unit) (j' PUnit.unit)))) ^ (-1 : ℤ) * res inf_le_right r,
      fun y hy => ?_⟩
    have t := gen_trans (D.psi_gen χ) (𝟙 (TK R).left) y (j := j) (j' := j') (hh hy.1) (h' hy.2)
    refine Eq.trans ?_ t.symm
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · refine (map_zpow _ _ _).trans (Eq.trans ?_ (Fintype.prod_unique _).symm)
      refine congrArg (· ^ (-1 : ℤ)) ((gm_res (jK R) y l hy _).trans ?_)
      refine (gm_pull (jK R) (D.c χ).left y _ (l hy) _).trans ?_
      rw [Category.id_comp]; rfl
    · refine (gm_res (jK R) y inf_le_right hy _).trans ?_
      have a := gm_pull (𝟙 (TK R).left) (jK R) y V' hy.2 r
      rw [Category.id_comp] at a
      exact a.symm.trans ((congrArg _ e).trans (gm_res (𝟙 (TK R).left) y h' hy.2 _))
  choose W hW hx u hu using loc
  obtain ⟨s, hs⟩ := glue_unit V W hW (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hx _⟩) u
    (fun a b y hy => by
      have e : res (inf_le_left : W a ⊓ W b ≤ W a) (u a) = res inf_le_right (u b) := by
        refine Units.ext (jK_app_injective _ (congrArg Units.val (?_ : pullU (jK R) _ _ = pullU (jK R) _ _)))
        refine unit_ext fun z hz => ?_
        have hz' : jK R z ∈ W a ⊓ W b := hz
        refine (gm_pull (𝟙 _) (jK R) z _ hz' _).trans (Eq.trans ?_ (gm_pull (𝟙 _) (jK R) z _ hz' _).symm)
        rw [Category.id_comp, gm_res _ z _ hz', gm_res _ z _ hz', hu a z hz'.1, hu b z hz'.2]
      exact (gm_res _ y _ hy _).symm.trans ((congrArg _ e).trans (gm_res _ y _ hy _)))
  refine ⟨s.val, s.isUnit, congrArg Units.val (?_ : pullU (jK R) V s = res hh ((D.psi χ).s j))⟩
  refine unit_ext fun z hz => ?_
  have hz' : jK R z ∈ V := hz
  refine (gm_pull (𝟙 _) (jK R) z _ hz' _).trans (Eq.trans ?_ (gm_res _ z hh hz _).symm)
  rw [Category.id_comp, ← gm_res _ z (hW ⟨_, hz'⟩) (hx ⟨_, hz'⟩), hs]
  exact hu _ z (hx ⟨_, hz'⟩)

theorem psiUnitOn_iff_interior (U : Set (Spec (CommRingCat.of R))) :
    PsiUnitOn D χ U ↔ TorusGraphMaps.PsiGenOn D χ (interior U) :=
  ⟨psiGenOn_interior_of_psiUnitOn D χ,
    fun h => (DegActCheck.psiUnitOn_iff_interior D χ U).2 (psiUnitOn_of_psiGenOn D χ h)⟩

theorem psiUnitOn_iff {U : Set (Spec (CommRingCat.of R))} (hU : IsOpen U) :
    PsiUnitOn D χ U ↔ TorusGraphMaps.PsiGenOn D χ U := by
  rw [psiUnitOn_iff_interior, hU.interior_eq]

end Unit

end GlobalTheory.DegActCompare
