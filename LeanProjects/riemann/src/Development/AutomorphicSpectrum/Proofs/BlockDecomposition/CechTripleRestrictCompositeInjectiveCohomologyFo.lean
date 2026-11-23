import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTripleRestrictCompositeInjectiveSecond

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R]

def secA {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (p : Pair φ) : Sec s p.1.2.1 →ₐ[R] Sec s' p.1.1.1 :=
  { secPull s s' p with commutes' := (semiHom_secPull h p).map_algebraMap }

theorem secA_apply {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (p : Pair φ) (x : Sec s p.1.2.1) :
    secA h p x = secPull s s' p x := rfl

theorem kunneth_open (A B : Over (Sp R)) (U : A.left.affineOpens) (V : B.left.affineOpens) :
    ∃ hV : IsAffineOpen ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1),
      Function.Bijective (Algebra.TensorProduct.lift
        (secA (wOver (fst A B)) ⟨(⟨_, hV⟩, U), inf_le_left⟩)
        (secA (wOver (snd A B)) ⟨(⟨_, hV⟩, V), inf_le_right⟩) (fun _ _ ↦ Commute.all _ _)) := by
  let Sa := Sec A.hom U.1
  let Sb := Sec B.hom V.1
  let iU := affPt A.hom U
  let iV := affPt B.hom V
  have eU : iU ≫ A.hom = spMap (algebraMap R Sa) := affPt_w _ _
  have eV : iV ≫ B.hom = spMap (algebraMap R Sb) := affPt_w _ _
  let ma : pullback (spMap (algebraMap R Sa)) (spMap (algebraMap R Sb)) ⟶ pullback A.hom B.hom :=
    pullback.map _ _ _ _ iU iV (𝟙 _) (by rw [Category.comp_id, eU]) (by rw [Category.comp_id, eV])
  haveI hma : IsOpenImmersion ma :=
    MorphismProperty.pullback_map (P := @IsOpenImmersion) (f := spMap (algebraMap R Sa)) (g := spMap (algebraMap R Sb))
      (IsAffineOpen.isOpenImmersion_fromSpec U.2) (IsAffineOpen.isOpenImmersion_fromSpec V.2) eU.symm eV.symm
  let j : Spec (CommRingCat.of (Sa ⊗[R] Sb)) ⟶ pullback A.hom B.hom := (pullbackSpecIso R Sa Sb).inv ≫ ma
  have hj : j.opensRange = (fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1 := by
    apply TopologicalSpace.Opens.ext
    have e1 : Set.range j = Set.range ma := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨(pullbackSpecIso R Sa Sb).inv y, (Scheme.Hom.comp_apply _ _ y).symm⟩
      · rintro ⟨y, rfl⟩
        refine ⟨(pullbackSpecIso R Sa Sb).hom y, ?_⟩
        simp [j, ← Scheme.Hom.comp_apply]
    have e2 := Scheme.Pullback.range_map (spMap (algebraMap R Sa)) (spMap (algebraMap R Sb)) A.hom B.hom iU iV (𝟙 _)
      (by rw [Category.comp_id, eU]) (by rw [Category.comp_id, eV])
    simp only [Scheme.Hom.coe_opensRange, e1]
    refine e2.trans ?_
    rw [show Set.range iU = (U.1 : Set A.left) from U.2.range_fromSpec, show Set.range iV = (V.1 : Set B.left) from V.2.range_fromSpec]
    rfl
  have hV : IsAffineOpen ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1) := hj ▸ isAffineOpen_opensRange j
  refine ⟨hV, ?_⟩
  let κ : Sa ⊗[R] Sb →ₐ[R] Sec (A ⊗ B).hom ((fst A B).left ⁻¹ᵁ U.1 ⊓ (snd A B).left ⁻¹ᵁ V.1) := Algebra.TensorProduct.lift
        (secA (wOver (fst A B)) ⟨(⟨_, hV⟩, U), inf_le_left⟩)
        (secA (wOver (snd A B)) ⟨(⟨_, hV⟩, V), inf_le_right⟩) (fun _ _ ↦ Commute.all _ _)
  have hk : spMap κ.toRingHom ≫ j = hV.fromSpec := by
    apply pullback.hom_ext
    · have s1 := secPull_affPt (φ := (fst A B).left) A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩
      have l : κ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = secPull A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩ :=
        RingHom.ext fun x ↦ by
          change κ (x ⊗ₜ 1) = _
          rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]; rfl
      have m1 : ma ≫ pullback.fst A.hom B.hom = pullback.fst _ _ ≫ iU := pullback.lift_fst _ _ _
      rw [Category.assoc, Category.assoc, m1, ← Category.assoc (pullbackSpecIso R Sa Sb).inv, pullbackSpecIso_inv_fst]
      have m2 : spMap κ.toRingHom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
          spMap (secPull A.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, U), inf_le_left⟩) := by
        rw [← l, spMap_comp]
      rw [← Category.assoc, m2]
      exact s1
    · have s1 := secPull_affPt (φ := (snd A B).left) B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩
      have l : κ.toRingHom.comp (Algebra.TensorProduct.includeRight : Sb →ₐ[R] Sa ⊗[R] Sb).toRingHom = secPull B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩ :=
        RingHom.ext fun x ↦ by
          change κ (1 ⊗ₜ x) = _
          rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]; rfl
      have m1 : ma ≫ pullback.snd A.hom B.hom = pullback.snd _ _ ≫ iV := pullback.lift_snd _ _ _
      rw [Category.assoc, Category.assoc, m1, ← Category.assoc (pullbackSpecIso R Sa Sb).inv, pullbackSpecIso_inv_snd]
      have m2 : spMap κ.toRingHom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Sb →ₐ[R] Sa ⊗[R] Sb).toRingHom) =
          spMap (secPull B.hom (A ⊗ B).hom ⟨(⟨_, hV⟩, V), inf_le_right⟩) := by
        rw [← l, spMap_comp]
      rw [← Category.assoc]
      exact (congrArg (· ≫ iV) m2).trans s1
  haveI hj1 : IsOpenImmersion j := inferInstance
  haveI h2 : IsOpenImmersion (spMap κ.toRingHom ≫ j) := hk ▸ IsAffineOpen.isOpenImmersion_fromSpec hV
  haveI h3 : IsOpenImmersion (spMap κ.toRingHom) := IsOpenImmersion.of_comp _ j
  have hs : Function.Surjective (spMap κ.toRingHom) := by
    intro t
    have ht : j t ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec, ← hj]; exact ⟨t, rfl⟩
    obtain ⟨y, hy⟩ := ht
    refine ⟨y, j.injective ?_⟩
    rw [← hy, ← hk]; rfl
  haveI : Epi (spMap κ.toRingHom).base := (TopCat.epi_iff_surjective _).2 hs
  haveI hi : IsIso (spMap κ.toRingHom) := IsOpenImmersion.isIso (spMap κ.toRingHom)
  haveI : IsIso (CommRingCat.ofHom κ.toRingHom) := by
    let g := Spec.preimage (inv (Spec.map (CommRingCat.ofHom κ.toRingHom)))
    refine ⟨g, Spec.map_injective ?_, Spec.map_injective ?_⟩ <;> simp [g]
  exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom κ.toRingHom)
end GlobalTheory.CompanionTheory.HopfSys

namespace GlobalTheory.CompanionTheory.HopfSys
section Comp
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {τ : R' →+* R''}
  {φ : X' ⟶ X} {ψ : X'' ⟶ X'}

theorem cechTripleRestrictComposite_comp_pairRestrict (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') (c : HO1 s'') :
    (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 c) =
      (CoefMap.restrict (OAff s'') (cechTripleProjFirstThird ψ φ ⋙ pairFst (ψ ≫ φ))).pull1 c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) c

theorem cechTripleRestrictComposite_injective_cohomology_forms (ψ : X'' ⟶ X') (φ : X' ⟶ X) (s'' : X'' ⟶ Sp R'') :
    Function.Injective (cechTripleRestrictComposite ψ φ s'').pull1 := by
  intro x y e
  obtain ⟨x0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 x
  obtain ⟨y0, rfl⟩ := (pairRes_bijective (ψ ≫ φ) s'').1.2 y
  rw [cechTripleRestrictComposite_comp_pairRestrict, cechTripleRestrictComposite_comp_pairRestrict] at e
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s''
  have hcov := triple_cover_affine ψ φ s''
  have hdir := exists_triple_below_two ψ φ s''
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s'') _ H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s'') _ H hcov hdir
  rw [_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg e]

theorem isPullO_comp (h : φ ≫ s = s' ≫ spMap σ) (h' : ψ ≫ s' = s'' ≫ spMap τ)
    (h'' : (ψ ≫ φ) ≫ s = s'' ≫ spMap (τ.comp σ)) {a : HO1 s} {a' : HO1 s'} {a'' : HO1 s''}
    (p : IsPullO h a a') (p' : IsPullO h' a' a'') : IsPullO h'' a a'' := by
  refine cechTripleRestrictComposite_injective_cohomology_forms ψ φ s'' ?_
  have p0 : (pairPull h).pull1 a = (pairRes φ s').pull1 a' := p
  have p1 : (pairPull h').pull1 a' = (pairRes ψ s'').pull1 a'' := p'
  have t1 : (cechTripleRestrictComposite ψ φ s'').pull1 ((pairPull h'').pull1 a) =
      (cechTriplePullbackSecond h').pull1 ((pairPull h).pull1 a) := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans ((pairPull h'').comp (cechTripleRestrictComposite ψ φ s''))
      ((pairPull h).comp (cechTriplePullbackSecond h')) { app U := 𝟙 _ } (fun U b ↦ by
        erw [mp_id]
        exact congrArg (fun q ↦ q.hom b) (Scheme.Hom.appLE_comp_appLE ψ φ U.unop.1.2.2.1 U.unop.1.2.1.1
          U.unop.1.1.1 U.unop.2.2 U.unop.2.1)) a
  have t2 : (cechTriplePullbackSecond (φ := φ) h').pull1 ((pairRes φ s').pull1 a') =
      (cechTripleRestrictFirst ψ φ s'').pull1 ((pairPull h').pull1 a') := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ by erw [mp_id]) a'
  have t3 : (cechTripleRestrictFirst ψ φ s'').pull1 ((pairRes ψ s'').pull1 a'') =
      (cechTripleRestrictComposite ψ φ s'').pull1 ((pairRes (ψ ≫ φ) s'').pull1 a'') := by
    rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ { app U := 𝟙 _ } (fun U b ↦ mp_id (OAff s'') _ b) a''
  rw [t1, p0, t2, p1, t3]
end Comp

section Over
variable {R : Type} [CommRing R]

theorem isPullO_over_comp {Y Z T : Over (Sp R)} (f : Y ⟶ Z) (g : Z ⟶ T) {a : HO1 T.hom} {a' : HO1 Z.hom}
    {a'' : HO1 Y.hom} (p : IsPullO (wOver g) a a') (p' : IsPullO (wOver f) a' a'') :
    IsPullO (wOver (f ≫ g)) a a'' :=
  isPullO_comp (wOver g) (wOver f) (wOver (f ≫ g)) p p'

theorem isPullO_over_id (Y : Over (Sp R)) (c : HO1 Y.hom) : IsPullO (wOver (𝟙 Y)) c c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull (wOver (𝟙 Y))) (pairRes _ Y.hom) (pairIdTrans Y.left) (fun _ _ ↦ rfl) c

theorem isPullO_sub {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
    {h : φ ≫ s = s' ≫ spMap (RingHom.id R)} {a b : HO1 s} {a' b' : HO1 s'} (ha : IsPullO h a a')
    (hb : IsPullO h b b') : IsPullO h (a - b) (a' - b') := by
  unfold IsPullO at *; rw [map_sub, map_sub, ha, hb]

theorem eq_zero_of_isAffine {X : Scheme.{0}} [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s) : c = 0 :=
  H1.eq_zero_of_isInitial (OAff s) (T₀ := op ⟨⊤, isAffineOpen_top _⟩)
    (Limits.IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top _⟩ from
        le_top (a := U.unop.1))).op) fun _ _ ↦ rfl) c

theorem isPullO_through_unit {Y Z : Over (Sp R)} (g : Y ⟶ 𝟙_ (Over (Sp R))) (e : 𝟙_ (Over (Sp R)) ⟶ Z)
    (c : HO1 Z.hom) : IsPullO (wOver (g ≫ e)) c 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))
  obtain ⟨c', hc', -⟩ := existsUnique_isPullO (wOver e) c
  rw [eq_zero_of_isAffine _ c'] at hc'
  exact isPullO_over_comp g e hc' ((map_zero _).trans (map_zero _).symm)

variable (A : Over (Sp R)) [GrpObj A]

theorem primitive_structure_sheaf_cohomology_class
    (hAx : ∀ c : HO1 (A ⊗ A).hom, IsPullO (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0 →
      IsPullO (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0 → c = 0) (c : HO1 A.hom) :
    pullHO1 (wOver μ[A]) c = pullHO1 (wOver (fst A A)) c + pullHO1 (wOver (snd A A)) c := by
  have hm := isPullO_pullHO1 (wOver μ[A]) c
  have hp := isPullO_pullHO1 (wOver (fst A A)) c
  have hq := isPullO_pullHO1 (wOver (snd A A)) c
  have one_def : (1 : A ⟶ A) = toUnit A ≫ η[A] := rfl
  have e1 : lift (𝟙 A) (1 : A ⟶ A) ≫ μ[A] = 𝟙 A := by
    rw [← Hom.mul_def, _root_.mul_one]
  have e2 : lift (1 : A ⟶ A) (𝟙 A) ≫ μ[A] = 𝟙 A := by
    rw [← Hom.mul_def, _root_.one_mul]
  have key : ∀ (f : A ⟶ A ⊗ A) {a b : HO1 A.hom}, f ≫ μ[A] = 𝟙 A →
      IsPullO (wOver (f ≫ fst A A)) c a → IsPullO (wOver (f ≫ snd A A)) c b → c - a - b = 0 →
      IsPullO (wOver f) (pullHO1 (wOver μ[A]) c - pullHO1 (wOver (fst A A)) c - pullHO1 (wOver (snd A A)) c) 0 := by
    intro f a b hμ ha hb hab
    have hcomp : ∀ (g : A ⊗ A ⟶ A) {w : HO1 A.hom}, IsPullO (wOver (f ≫ g)) c w →
        IsPullO (wOver f) (pullHO1 (wOver g) c) w := fun g w hw ↦ by
      have h1 := isPullO_pullHO1 (wOver f) (pullHO1 (wOver g) c)
      have h2 := isPullO_over_comp f g (isPullO_pullHO1 (wOver g) c) h1
      rwa [hw.eq_pullHO1.trans h2.eq_pullHO1.symm]
    have h0 : IsPullO (wOver (f ≫ μ[A])) c c := by rw [hμ]; exact isPullO_over_id _ c
    have := isPullO_sub (isPullO_sub (hcomp μ[A] h0) (hcomp (fst A A) ha)) (hcomp (snd A A) hb)
    rwa [hab] at this
  have z1 := key (lift (𝟙 A) (1 : A ⟶ A)) (a := c) (b := 0) e1
    (by rw [lift_fst]; exact isPullO_over_id _ c)
    (by rw [lift_snd, one_def]; exact isPullO_through_unit _ _ c) (by simp)
  have z2 := key (lift (1 : A ⟶ A) (𝟙 A)) (a := 0) (b := c) e2
    (by rw [lift_fst, one_def]; exact isPullO_through_unit _ _ c)
    (by rw [lift_snd]; exact isPullO_over_id _ c) (by simp)
  have z := hAx _ z1 z2
  rw [sub_sub, sub_eq_zero] at z
  exact z
end Over
end GlobalTheory.CompanionTheory.HopfSys

namespace GlobalTheory.CompanionTheory.HopfSys
section Lift
variable {R : Type} [CommRing R] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {C D : Type} [Category.{0} C] [Category.{0} D]

def pairFn (φ : X' ⟶ X) (u : C ⥤ AffOp X) (t : D ⥤ C) (fb : D ⥤ AffOp X')
    (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) : D ⥤ (Pair φ)ᵒᵖ where
  obj d := op ⟨((fb.obj d).unop, (u.obj (t.obj d)).unop), hle d⟩
  map {d d'} a := (homOfLE (show (⟨((fb.obj d').unop, (u.obj (t.obj d')).unop), hle d'⟩ : Pair φ) ≤
    ⟨((fb.obj d).unop, (u.obj (t.obj d)).unop), hle d⟩ from
    Prod.le_def.2 ⟨leOfHom (fb.map a).unop, leOfHom (u.map (t.map a)).unop⟩)).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def liftAlong (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (u : C ⥤ AffOp X) (t : D ⥤ C) (fb : D ⥤ AffOp X')
    (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) :
    CoefMap (RingHom.id R) (u ⋙ OAff s) (fb ⋙ OAff s') where
  G := t
  α d := (pairPull h).α ((pairFn φ u t fb hle).obj d)
  naturality a b := (pairPull h).naturality ((pairFn φ u t fb hle).map a) b
  smul d := (pairPull h).smul ((pairFn φ u t fb hle).obj d)

theorem liftAlong_pull1 (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (u : C ⥤ AffOp X) (t : D ⥤ C)
    (fb : D ⥤ AffOp X') (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) (c : HO1 s) :
    (liftAlong h u t fb hle).pull1 ((CoefMap.restrict (OAff s) u).pull1 c) =
      (CoefMap.restrict (OAff s') fb).pull1 (pullHO1 h c) := by
  let r : CoefMap (RingHom.id R) (OPair φ s') (fb ⋙ OAff s') :=
    { G := pairFn φ u t fb hle
      α _ := RingHom.id _
      naturality _ _ := rfl
      smul _ _ _ := rfl }
  have t1 : (liftAlong h u t fb hle).pull1 ((CoefMap.restrict (OAff s) u).pull1 c) =
      r.pull1 ((pairPull h).pull1 c) := by
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c; rfl
  have t2 : ∀ x : HO1 s', r.pull1 ((pairRes φ s').pull1 x) = (CoefMap.restrict (OAff s') fb).pull1 x := by
    intro x
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ x; rfl
  rw [t1, (isPullO_pullHO1 h c : _ = _), t2]
end Lift
end GlobalTheory.CompanionTheory.HopfSys

namespace GlobalTheory.CompanionTheory.HopfSys
section Aff

theorem aff_inf_preimage {X Y T : Scheme.{0}} (s : Y ⟶ T) [IsSeparated s] [IsAffine T] (f : X ⟶ Y) {V : X.Opens}
    (hV : IsAffineOpen V) {U : Y.Opens} (hU : IsAffineOpen U) : IsAffineOpen (V ⊓ f ⁻¹ᵁ U) := by
  haveI : IsAffine V := hV
  haveI : IsAffineHom (V.ι ≫ f) := by
    haveI : IsAffineHom ((V.ι ≫ f) ≫ s) := inferInstance
    exact IsAffineHom.of_comp _ s
  have := (hU.preimage (V.ι ≫ f)).image_of_isOpenImmersion V.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at this
end Aff
end GlobalTheory.CompanionTheory.HopfSys

namespace GlobalTheory.CompanionTheory.HopfSys
section Main
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)

def Vop (a b : P) : (A ⊗ A).left.Opens := (fst A A).left ⁻¹ᵁ (S.u a).1 ⊓ (snd A A).left ⁻¹ᵁ (S.u b).1

def Wop (a b c : P) : (A ⊗ A).left.Opens := Vop A S a b ⊓ μ[A].left ⁻¹ᵁ (S.u c).1

theorem Vop_aff (a b : P) : IsAffineOpen (Vop A S a b) := (kunneth_open A A (S.u a) (S.u b)).choose

theorem Wop_aff [IsSeparated A.hom] (a b c : P) : IsAffineOpen (Wop A S a b c) :=
  aff_inf_preimage A.hom _ (Vop_aff A S a b) (S.u c).2

theorem Wop_mono {a a' b b' c c' : P} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    Wop A S a' b' c' ≤ Wop A S a b c := fun _ hx ↦
  ⟨⟨S.mono ha hx.1.1, S.mono hb hx.1.2⟩, S.mono hc hx.2⟩

variable [IsSeparated A.hom]

def wFn : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ ⥤ AffOp (A ⊗ A).left where
  obj T := op ⟨Wop A S T.1.1.unop T.1.2.unop T.2.unop, Wop_aff A S _ _ _⟩
  map {T T'} f := (homOfLE (show (⟨Wop A S T'.1.1.unop T'.1.2.unop T'.2.unop, Wop_aff A S _ _ _⟩ :
      (A ⊗ A).left.affineOpens) ≤ ⟨Wop A S T.1.1.unop T.1.2.unop T.2.unop, Wop_aff A S _ _ _⟩ from
    Wop_mono A S (leOfHom f.1.1.unop) (leOfHom f.1.2.unop) (leOfHom f.2.unop))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

abbrev GG : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ ⥤ CommAlgCat.{0} R := wFn A S ⋙ OAff (A ⊗ A).hom

def pMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver (fst A A)) S.fn (CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.fst _ _) (wFn A S)
    fun _ _ hx ↦ hx.1.1

def qMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver (snd A A)) S.fn (CategoryTheory.Prod.fst _ _ ⋙ CategoryTheory.Prod.snd _ _) (wFn A S)
    fun _ _ hx ↦ hx.1.2

def mMap : CoefMap (RingHom.id R) (OSys A.hom S) (GG A S) :=
  liftAlong (wOver μ[A]) S.fn (CategoryTheory.Prod.snd _ _) (wFn A S) fun _ _ hx ↦ hx.2

end Main

section
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

def toAlg (m : CoefMap (RingHom.id R) F G) (T : D) : F.obj (m.G.obj T) →ₐ[R] G.obj T :=
  { m.α T with
    commutes' := fun r ↦ by
      change m.α T _ = _
      rw [Algebra.algebraMap_eq_smul_one, m.smul, map_one, ← Algebra.algebraMap_eq_smul_one]
      rfl }

theorem toAlg_apply (m : CoefMap (RingHom.id R) F G) (T : D) (x : F.obj (m.G.obj T)) :
    toAlg m T x = m.α T x := rfl
end

section Main2
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]

def pA (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (OSys A.hom S).obj T.1.1 →ₐ[R] (GG A S).obj T := toAlg (pMap A S) T

def qA (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (OSys A.hom S).obj T.1.2 →ₐ[R] (GG A S).obj T := toAlg (qMap A S) T

def pjAlg (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) : (box (OSys A.hom S)).obj T.1 →ₐ[R] (GG A S).obj T :=
  Algebra.TensorProduct.lift (pA A S T) (qA A S T) fun _ _ ↦ Commute.all _ _

theorem pjAlg_tmul (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ) (x : (OSys A.hom S).obj T.1.1) (y : (OSys A.hom S).obj T.1.2) :
    pjAlg A S T (x ⊗ₜ[R] y) = pA A S T x * qA A S T y :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

def pj : Proj (box (OSys A.hom S)) (GG A S) where
  α T := pjAlg A S T
  naturality {T T'} φ b := by
    have e : (pjAlg A S T').comp (mp (box (OSys A.hom S)) φ.1) = (mp (GG A S) φ).comp (pjAlg A S T) :=
      Algebra.TensorProduct.ext' fun x y ↦ by
        change pjAlg A S T' (mp (OSys A.hom S) φ.1.1 x ⊗ₜ[R] mp (OSys A.hom S) φ.1.2 y) =
          mp (GG A S) φ (pjAlg A S T (x ⊗ₜ[R] y))
        rw [pjAlg_tmul, pjAlg_tmul, map_mul]
        exact congrArg₂ (· * ·) ((pMap A S).naturality φ x) ((qMap A S).naturality φ y)
    exact congrArg (fun t ↦ t b) e

end Main2
end GlobalTheory.CompanionTheory.HopfSys

namespace GlobalTheory.CompanionTheory.HopfSys
section Main3
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)

def kap (a b : P) : Sec A.hom (S.u a).1 ⊗[R] Sec A.hom (S.u b).1 →ₐ[R] Sec (A ⊗ A).hom (Vop A S a b) :=
  Algebra.TensorProduct.lift (secA (wOver (fst A A)) ⟨(⟨_, Vop_aff A S a b⟩, S.u a), inf_le_left⟩)
    (secA (wOver (snd A A)) ⟨(⟨_, Vop_aff A S a b⟩, S.u b), inf_le_right⟩) fun _ _ ↦ Commute.all _ _

theorem kap_bijective (a b : P) : Function.Bijective (kap A S a b) :=
  (kunneth_open A A (S.u a) (S.u b)).choose_spec

variable [IsSeparated A.hom]

theorem pjAlg_apply (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ)
    (z : (OSys A.hom S).obj T.1.1 ⊗[R] (OSys A.hom S).obj T.1.2) :
    pjAlg A S T z = Sec.res (A ⊗ A).hom
      (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)
      (kap A S T.1.1.unop T.1.2.unop z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)).symm)
  | tmul x y =>
    rw [pjAlg_tmul]
    refine Eq.trans ?_ (congrArg _ (Algebra.TensorProduct.lift_tmul _ _ _ _ _).symm)
    refine Eq.trans ?_ (map_mul _ _ _).symm
    refine congrArg₂ (· * ·) ?_ ?_
    · exact congrArg (fun t ↦ t.hom x) ((fst A A).left.appLE_map (U := (S.u T.1.1.unop).1) (V := Vop A S T.1.1.unop T.1.2.unop) inf_le_left
        (homOfLE (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)).op).symm
    · exact congrArg (fun t ↦ t.hom y) ((snd A A).left.appLE_map (U := (S.u T.1.2.unop).1) (V := Vop A S T.1.1.unop T.1.2.unop) inf_le_right
        (homOfLE (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)).op).symm

theorem Wop_inf (a b c c' : P) : Wop A S a b (c ⊓ c') = Wop A S a b c ⊓ Wop A S a b c' := by
  apply le_antisymm
  · exact le_inf (Wop_mono A S le_rfl le_rfl inf_le_left) (Wop_mono A S le_rfl le_rfl inf_le_right)
  · intro x hx
    refine ⟨hx.1.1, ?_⟩
    change μ[A].left x ∈ (S.u (c ⊓ c')).1
    rw [S.map_inf]
    exact ⟨hx.1.2, hx.2.2⟩

theorem Wop_iSup (a b : P) : ⨆ c, Wop A S a b c = Vop A S a b := by
  apply le_antisymm (iSup_le fun c ↦ inf_le_left)
  intro x hx
  have h1 : μ[A].left x ∈ ⨆ c, (S.u c).1 := by rw [S.cover]; trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, hx, hc⟩

theorem pj_qiso [Finite P] (hF : FubiniSt) (hA : AffAcycSt) : AllQIso (pj A S).coef := by
  haveI : Quiver.IsThin (Pᵒᵖ × Pᵒᵖ) := fun _ _ ↦ ⟨fun f g ↦ Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  refine hF R (Pᵒᵖ × Pᵒᵖ) (box (OSys A.hom S)) Pᵒᵖ (GG A S) (pj A S) fun T ↦ ?_
  let u : P →o (A ⊗ A).left.affineOpens := ⟨fun c ↦ ⟨Wop A S T.1.unop T.2.unop c, Wop_aff A S _ _ _⟩,
    fun c c' h ↦ Wop_mono A S le_rfl le_rfl h⟩
  obtain ⟨h1, h2, h3⟩ := hA R (A ⊗ A).left (A ⊗ A).hom ⟨Vop A S T.1.unop T.2.unop, Vop_aff A S _ _⟩ P u
    (fun c ↦ inf_le_left) (fun c c' ↦ Wop_inf A S _ _ c c') (Wop_iSup A S _ _)
  let aug : Sec (A ⊗ A).hom (Vop A S T.1.unop T.2.unop) →ₗ[R] Cn (u.monotone.functor.op ⋙ OAff (A ⊗ A).hom) 0 :=
    LinearMap.pi fun c ↦ (Sec.res (A ⊗ A).hom (show (u (c.obj (Fin.last 0)).unop).1 ≤ Vop A S T.1.unop T.2.unop from inf_le_left)).toLinearMap
  have hf : ∀ z c, ((pj A S).fib T z) c = aug (kap A S T.1.unop T.2.unop z) c := fun z c ↦
    pjAlg_apply A S (T, c.obj (Fin.last 0)) z
  have hb := kap_bijective A S T.1.unop T.2.unop
  refine ⟨fun x y e ↦ hb.1 (h1 (funext fun c ↦ ?_)), fun y ↦ (h2 y).trans ?_, h3⟩
  · exact ((hf x c).symm.trans (congrFun e c)).trans (hf y c)
  · constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, rfl⟩ := hb.2 w
      exact ⟨z, funext fun c ↦ hf z c⟩
    · rintro ⟨z, rfl⟩
      exact ⟨kap A S T.1.unop T.2.unop z, funext fun c ↦ (hf z c).symm⟩
end Main3
end GlobalTheory.CompanionTheory.HopfSys

namespace GlobalTheory.CompanionTheory.HopfSys
section AutomorphyRankFourMain
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]

theorem pMap_pull1 (x : H1 (OSys A.hom S)) :
    (pMap A S).pull1 x = (pj A S).coef.pull1 ((boxL (OSys A.hom S)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans (pMap A S) ((boxL (OSys A.hom S)).comp (pj A S).coef) { app _ := 𝟙 _ } (fun T b ↦ ?_) x
  erw [mp_id]
  refine (pjAlg_tmul A S T b 1).trans ?_
  rw [map_one, _root_.mul_one]
  rfl

theorem qMap_pull1 (x : H1 (OSys A.hom S)) :
    (qMap A S).pull1 x = (pj A S).coef.pull1 ((boxR (OSys A.hom S)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans (qMap A S) ((boxR (OSys A.hom S)).comp (pj A S).coef) { app _ := 𝟙 _ } (fun T b ↦ ?_) x
  erw [mp_id]
  refine (pjAlg_tmul A S T 1 b).trans ?_
  rw [map_one, _root_.one_mul]
  rfl

theorem primitive
    (hAx : ∀ c : HO1 (A ⊗ A).hom, IsPullO (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0 →
      IsPullO (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0 → c = 0)
    (hs : Function.Surjective (resSys A.hom S).pull1) (c : H1 (OSys A.hom S)) :
    (mMap A S).pull1 c = (pj A S).coef.pull1 ((boxL (OSys A.hom S)).pull1 c + (boxR (OSys A.hom S)).pull1 c) := by
  obtain ⟨c, rfl⟩ := hs c
  rw [map_add, ← pMap_pull1, ← qMap_pull1]
  have hm : (mMap A S).pull1 ((resSys A.hom S).pull1 c) = _ := liftAlong_pull1 (wOver μ[A]) S.fn _ (wFn A S) _ c
  have hp : (pMap A S).pull1 ((resSys A.hom S).pull1 c) = _ := liftAlong_pull1 (wOver (fst A A)) S.fn _ (wFn A S) _ c
  have hq : (qMap A S).pull1 ((resSys A.hom S).pull1 c) = _ := liftAlong_pull1 (wOver (snd A A)) S.fn _ (wFn A S) _ c
  rw [hm, hp, hq, ← map_add, primitive_structure_sheaf_cohomology_class A hAx]

theorem exists_unit_mem (hR : IsField R) : ∃ a₀, η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤ := by
  letI := hR.toField
  haveI hu : Unique (𝟙_ (Over (Sp R))).left := inferInstanceAs (Unique (PrimeSpectrum R))
  have h1 : η[A].left default ∈ ⨆ a, (S.u a).1 := by rw [S.cover]; trivial
  obtain ⟨a₀, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
  refine ⟨a₀, top_le_iff.1 fun x _ ↦ ?_⟩
  rw [Subsingleton.elim x default]
  exact ha

theorem appLE_chain {X Y Z : Scheme.{0}} (ψ : X ⟶ Y) (φ : Y ⟶ Z) (χ : X ⟶ Z) (hχ : ψ ≫ φ = χ) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e1 : V ≤ φ ⁻¹ᵁ U) (e2 : W ≤ ψ ⁻¹ᵁ V) (e3 : W ≤ χ ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (ψ.appLE V W e2).hom ((φ.appLE U V e1).hom x) = (χ.appLE U W e3).hom x := by
  subst hχ
  exact congrArg (fun t ↦ t.hom x) (Scheme.Hom.appLE_comp_appLE ψ φ U V W e1 e2)

theorem appLE_id {X : Scheme.{0}} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U e).hom x = x := by
  have h : X.presheaf.map (homOfLE e).op = 𝟙 _ := by
    rw [show (homOfLE e).op = 𝟙 (op U) from Subsingleton.elim _ _]; exact X.presheaf.map_id _
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [h]
  rfl

end AutomorphyRankFourMain
end GlobalTheory.CompanionTheory.HopfSys

namespace GlobalTheory.CompanionTheory.HopfSys
section Main5
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]

abbrev iota : A ⟶ A ⊗ A := lift (1 : A ⟶ A) (𝟙 A)

def tK (a₀ : P) : Pᵒᵖ ⥤ (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ where
  obj b := ((op a₀, b), b)
  map f := ((𝟙 _, f), f)

theorem iota_fst : (iota A).left ≫ (fst A A).left = A.hom ≫ η[A].left :=
  congrArg (fun f ↦ f.left) (lift_fst (1 : A ⟶ A) (𝟙 A))

theorem iota_snd : (iota A).left ≫ (snd A A).left = 𝟙 _ :=
  congrArg (fun f ↦ f.left) (lift_snd (1 : A ⟶ A) (𝟙 A))

theorem iota_mul : (iota A).left ≫ μ[A].left = 𝟙 _ :=
  congrArg (fun f ↦ f.left) ((Hom.mul_def (1 : A ⟶ A) (𝟙 A)).symm.trans (_root_.one_mul (𝟙 A)))

variable {A S}

theorem kle {a₀ : P} (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) :
    (S.fn.obj b).unop.1 ≤ (iota A).left ⁻¹ᵁ ((wFn A S).obj ((tK a₀).obj b)).unop.1 := by
  intro x hx
  have h1 : (fst A A).left ((iota A).left x) ∈ (S.u a₀).1 := by
    have : (fst A A).left ((iota A).left x) = η[A].left (A.hom x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, iota_fst]
    rw [this]
    have h2 : A.hom x ∈ η[A].left ⁻¹ᵁ (S.u a₀).1 := by rw [ha]; trivial
    exact h2
  have h2 : (snd A A).left ((iota A).left x) = x := by
    rw [← Scheme.Hom.comp_apply, iota_snd]; rfl
  have h3 : μ[A].left ((iota A).left x) = x := by
    rw [← Scheme.Hom.comp_apply, iota_mul]; rfl
  refine ⟨⟨h1, ?_⟩, ?_⟩
  · change (snd A A).left ((iota A).left x) ∈ (S.u b.unop).1
    rw [h2]; exact hx
  · change μ[A].left ((iota A).left x) ∈ (S.u b.unop).1
    rw [h3]; exact hx

def kMap {a₀ : P} (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : CoefMap (RingHom.id R) (GG A S) (OSys A.hom S) :=
  liftAlong (wOver (iota A)) (wFn A S) (tK a₀) S.fn (kle ha)
end Main5
end GlobalTheory.CompanionTheory.HopfSys

namespace GlobalTheory.CompanionTheory.HopfSys
section Main6
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {P : Type} [SemilatticeInf P] {S : Sys A.left P}
  [IsSeparated A.hom] {a₀ : P}

theorem unit_isAffine : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))

attribute [local instance] unit_isAffine

theorem unit_bijective (R : Type) [CommRing R] : Function.Bijective (algebraMap R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

def ptPair (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : Pair η[A].left := ⟨(⟨⊤, isAffineOpen_top _⟩, S.u a₀), ha.ge⟩

def epsA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) : (OSys A.hom S).obj (op a₀) →ₐ[R] R :=
  (AlgEquiv.ofBijective (Algebra.ofId R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) (unit_bijective R)).symm.toAlgHom.comp
    (secA (wOver η[A]) (ptPair ha) : Sec A.hom (S.u a₀).1 →ₐ[R] Sec (𝟙_ (Over (Sp R))).hom ⊤)

theorem algebraMap_epsA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (x : (OSys A.hom S).obj (op a₀)) :
    algebraMap R (Sec (𝟙_ (Over (Sp R))).hom ⊤) (epsA ha x) = secA (wOver η[A]) (ptPair ha) x :=
  (AlgEquiv.ofBijective (Algebra.ofId R (Sec (𝟙_ (Over (Sp R))).hom ⊤)) (unit_bijective R)).apply_symm_apply
    (secA (wOver η[A]) (ptPair ha) x)

theorem kMap_qA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) (y : (OSys A.hom S).obj b) :
    (kMap ha).α b (qA A S ((tK a₀).obj b) y) = y :=
  (appLE_chain (iota A).left (snd A A).left (𝟙 _) (iota_snd A) _ _ le_rfl y).trans (appLE_id _ _ y)

theorem kMap_mMap (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) (y : (OSys A.hom S).obj b) :
    (kMap ha).α b ((mMap A S).α ((tK a₀).obj b) y) = y :=
  (appLE_chain (iota A).left μ[A].left (𝟙 _) (iota_mul A) _ _ le_rfl y).trans (appLE_id _ _ y)

theorem kMap_pA (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ) (x : (OSys A.hom S).obj (op a₀)) :
    (kMap ha).α b (pA A S ((tK a₀).obj b) x) = algebraMap R ((OSys A.hom S).obj b) (epsA ha x) := by
  let tU := secA (wOver (toUnit A)) (⟨(S.u b.unop, ⟨⊤, isAffineOpen_top _⟩), le_top⟩ : Pair (toUnit A).left)
  have h1 : algebraMap R ((OSys A.hom S).obj b) (epsA ha x) = tU (secA (wOver η[A]) (ptPair ha) x) := by
    rw [← algebraMap_epsA]
    exact (tU.commutes _).symm
  rw [h1]
  have hE : ∀ W : A.left.Opens, W ≤ (A.hom ≫ η[A].left) ⁻¹ᵁ (S.u a₀).1 := fun W x _ ↦ by
    have h2 : A.hom x ∈ η[A].left ⁻¹ᵁ (S.u a₀).1 := by rw [ha]; trivial
    exact h2
  exact (appLE_chain (iota A).left (fst A A).left (A.hom ≫ η[A].left) (iota_fst A) _ _ (hE _) x).trans
    (appLE_chain A.hom η[A].left (A.hom ≫ η[A].left) rfl _ _ (hE _) x).symm

theorem evL_eq (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (b : Pᵒᵖ)
    (z : (OSys A.hom S).obj (op a₀) ⊗[R] (OSys A.hom S).obj b) :
    evL (OSys A.hom S) (op a₀) b (epsA ha) z = (kMap ha).α b (pjAlg A S ((tK a₀).obj b) z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _)).symm)
  | tmul x y =>
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg _ (pjAlg_tmul A S ((tK a₀).obj b) x y).symm)
    refine Eq.trans ?_ (map_mul _ _ _).symm
    rw [kMap_pA, kMap_qA]
    rfl

theorem counit (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (y : H2 (OSys A.hom S)) (w : H2 (box (OSys A.hom S)))
    (e : (pj A S).coef.pull2 w = (mMap A S).pull2 y) :
    (boxE (OSys A.hom S) (op a₀) (epsA ha)).pull2 w = y := by
  have e' := congrArg (kMap ha).pull2 e
  rw [← CoefMap.pullCohomologyTwo_comp, ← CoefMap.pullCohomologyTwo_comp] at e'
  have l1 : ((pj A S).coef.comp (kMap ha)).pull2 w = (boxE (OSys A.hom S) (op a₀) (epsA ha)).pull2 w := by
    let θ : ((pj A S).coef.comp (kMap ha)).G ⟶ (boxE (OSys A.hom S) (op a₀) (epsA ha)).G :=
      { app := fun b ↦ 𝟙 ((CategoryTheory.Prod.sectR (op a₀) Pᵒᵖ).obj b)
        naturality := fun _ _ f ↦ Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _) }
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((pj A S).coef.comp (kMap ha)) (boxE (OSys A.hom S) (op a₀) (epsA ha)) θ (fun b z ↦ ?_) w
    erw [mp_id]
    exact evL_eq ha b z
  have l2 : ((mMap A S).comp (kMap ha)).pull2 y = (CoefMap.id (OSys A.hom S)).pull2 y := by
    let θ : ((mMap A S).comp (kMap ha)).G ⟶ (CoefMap.id (OSys A.hom S)).G :=
      { app := fun b ↦ 𝟙 b
        naturality := fun _ _ f ↦ Subsingleton.elim _ _ }
    refine CoefMap.pullCohomologyTwo_eq_of_natTrans ((mMap A S).comp (kMap ha)) (CoefMap.id (OSys A.hom S)) θ (fun b z ↦ ?_) y
    erw [mp_id]
    exact (kMap_mMap ha b z).symm
  rw [← l1, e', l2, CoefMap.pullCohomologyTwo_id]
end Main6

theorem hopfSt : HtpySt → QCalcSt → FubiniSt → AffAcycSt → DescentSt → LowSt → AxOSt → HopfSt := by
  intro _ _ hF hA hD hL hX R _ A _ g hab hsm P _ _ S
  haveI := hab.proper
  haveI : IsSeparated A.hom := inferInstance
  refine ⟨(Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ, inferInstance, GG A S, (pj A S).coef, mMap A S, pj_qiso A S hF hA,
    primitive A S (hX R A g hab hsm) (hL R _ _ _ _ (resSys A.hom S) (hD R A.left A.hom inferInstance P S)).1.2, fun hR ↦ ?_⟩
  obtain ⟨a₀, ha⟩ := exists_unit_mem A S hR
  exact ⟨op a₀, epsA ha, fun y w e ↦ counit ha y w e⟩
end GlobalTheory.CompanionTheory.HopfSys
