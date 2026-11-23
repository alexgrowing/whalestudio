import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

namespace UpperTheory.YonedaTruncation

section Abs
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private lemma Q_map_eq {K L : CochainComplex C ℤ} (u : K ⟶ L) :
    DerivedCategory.Q.map u = (DerivedCategory.quotientCompQhIso C).inv.app K ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map u) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app L := by
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality u
  have e : (DerivedCategory.quotientCompQhIso C).inv.app K ≫ (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := by simp
  calc DerivedCategory.Q.map u = ((DerivedCategory.quotientCompQhIso C).inv.app K ≫ (DerivedCategory.quotientCompQhIso C).hom.app K) ≫ DerivedCategory.Q.map u := by rw [e, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, ← h]
      rfl

private noncomputable def tr {K T : CochainComplex C ℤ} {n : ℤ} (x : Cocycle K T n) :
    DerivedCategory.Q.obj K ⟶ (CategoryTheory.shiftFunctor _ n).obj (DerivedCategory.Q.obj T) :=
  DerivedCategory.Q.map (Cocycle.equivHomShift.symm x) ≫ (DerivedCategory.Q.commShiftIso n).hom.app T

private lemma tr_eq {K T : CochainComplex C ℤ} {n : ℤ} (x : Cocycle K T n) :
    tr x = (DerivedCategory.quotientCompQhIso C).inv.app K ≫
      DerivedCategory.Qh.map (CohomologyClass.toHom (CohomologyClass.mk x)) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app (T⟦n⟧) ≫ (DerivedCategory.Q.commShiftIso n).hom.app T := by
  rw [tr, Q_map_eq, CohomologyClass.toHom_mk]
  simp only [Category.assoc]

private lemma tr_congr {K T : CochainComplex C ℤ} {n : ℤ} {x x' : Cocycle K T n}
    (h : CohomologyClass.mk x = CohomologyClass.mk x') : tr x = tr x' := by
  rw [tr_eq, tr_eq, h]

private lemma tr_inj {K T : CochainComplex C ℤ} [T.IsKInjective] {n : ℤ} {x x' : Cocycle K T n}
    (h : tr x = tr x') : CohomologyClass.mk x = CohomologyClass.mk x' := by
  rw [tr_eq, tr_eq] at h
  have h1 := (cancel_epi _).1 h
  have h2 := (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app (T⟦n⟧) ≫ (DerivedCategory.Q.commShiftIso n).hom.app T)).1 h1
  exact (CohomologyClass.toHom_bijective K T n).1 ((CochainComplex.IsKInjective.Qh_map_bijective _ (T⟦n⟧)).1 h2)

private lemma tr_surj {K T : CochainComplex C ℤ} [T.IsKInjective] {n : ℤ}
    (z : DerivedCategory.Q.obj K ⟶ (CategoryTheory.shiftFunctor _ n).obj (DerivedCategory.Q.obj T)) :
    ∃ x : Cocycle K T n, tr x = z := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient C _).obj K) (T⟦n⟧)).2
    ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ z ≫ (DerivedCategory.Q.commShiftIso n).inv.app T ≫
      (DerivedCategory.quotientCompQhIso C).inv.app (T⟦n⟧))
  obtain ⟨c, rfl⟩ := (CohomologyClass.toHom_bijective K T n).2 g
  obtain ⟨x, rfl⟩ := c.mk_surjective
  refine ⟨x, ?_⟩
  rw [tr_eq, hg]
  simp

private noncomputable def dm (A : C) (T : CochainComplex C ℤ) (n : ℤ) (f : A ⟶ T.X n) (hf : f ≫ T.d n (n + 1) = 0) :
    (DerivedCategory.singleFunctor C 0).obj A ⟶ (CategoryTheory.shiftFunctor _ n).obj (DerivedCategory.Q.obj T) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app A ≫ tr (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)

private lemma mk_eq_iff {A : C} {T : CochainComplex C ℤ} {n : ℤ} {f f' : A ⟶ T.X n}
    (hf : f ≫ T.d n (n + 1) = 0) (hf' : f' ≫ T.d n (n + 1) = 0) :
    CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf) =
        CohomologyClass.mk (Cocycle.fromSingleMk f' (zero_add n) (n + 1) rfl hf') ↔
      ∃ g : A ⟶ T.X (n - 1), g ≫ T.d (n - 1) n = f - f' := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    ← Cocycle.fromSingleMk_sub _ _ _ _ _ hf hf',
    Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (n - 1) (by lia)]

private lemma dm_congr {A : C} {T : CochainComplex C ℤ} {n : ℤ} {f f' : A ⟶ T.X n}
    (hf : f ≫ T.d n (n + 1) = 0) (hf' : f' ≫ T.d n (n + 1) = 0) (h : f = f') : dm A T n f hf = dm A T n f' hf' := by
  subst h
  rfl

private lemma dm_eq {A : C} {T : CochainComplex C ℤ} {n : ℤ} {f f' : A ⟶ T.X n}
    (hf : f ≫ T.d n (n + 1) = 0) (hf' : f' ≫ T.d n (n + 1) = 0)
    (h : ∃ g : A ⟶ T.X (n - 1), g ≫ T.d (n - 1) n = f - f') : dm A T n f hf = dm A T n f' hf' := by
  rw [dm, dm, tr_congr ((mk_eq_iff hf hf').2 h)]

private lemma dm_inj {A : C} {T : CochainComplex C ℤ} [T.IsKInjective] {n : ℤ} {f f' : A ⟶ T.X n}
    (hf : f ≫ T.d n (n + 1) = 0) (hf' : f' ≫ T.d n (n + 1) = 0)
    (h : dm A T n f hf = dm A T n f' hf') : ∃ g : A ⟶ T.X (n - 1), g ≫ T.d (n - 1) n = f - f' := by
  rw [dm, dm] at h
  exact (mk_eq_iff hf hf').1 (tr_inj ((cancel_epi _).1 h))

private lemma dm_surj {A : C} {T : CochainComplex C ℤ} [T.IsKInjective] {n : ℤ}
    (z : (DerivedCategory.singleFunctor C 0).obj A ⟶ (CategoryTheory.shiftFunctor _ n).obj (DerivedCategory.Q.obj T)) :
    ∃ (f : A ⟶ T.X n) (hf : f ≫ T.d n (n + 1) = 0), dm A T n f hf = z := by
  obtain ⟨x, hx⟩ := tr_surj (K := (CochainComplex.singleFunctor C 0).obj A) (T := T) (n := n)
    ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app A ≫ z)
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (zero_add n) (n + 1) rfl
  refine ⟨f, hf, ?_⟩
  rw [dm, hx]
  simp

private lemma dm_pre {A A' : C} (a : A' ⟶ A) {T : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ T.X n)
    (hf : f ≫ T.d n (n + 1) = 0) (hf' : (a ≫ f) ≫ T.d n (n + 1) = 0) :
    dm A' T n (a ≫ f) hf' = (DerivedCategory.singleFunctor C 0).map a ≫ dm A T n f hf := by
  have h := Cocycle.fromSingleMk_precomp a f (zero_add n) (n + 1) rfl hf
  rw [dm, dm, tr, tr, h, Cocycle.equivHomShift_symm_precomp, Functor.map_comp]
  have h2 := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality a
  simp only [Category.assoc]
  exact (by simpa using congrArg (fun t => t ≫ DerivedCategory.Q.map (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) ≫ (DerivedCategory.Q.commShiftIso n).hom.app T) h2.symm)

private lemma dm_post {A : C} {T T' : CochainComplex C ℤ} (φ : T ⟶ T') {n : ℤ} (f : A ⟶ T.X n)
    (hf : f ≫ T.d n (n + 1) = 0) (hf' : (f ≫ φ.f n) ≫ T'.d n (n + 1) = 0) :
    dm A T' n (f ≫ φ.f n) hf' = dm A T n f hf ≫ (CategoryTheory.shiftFunctor _ n).map (DerivedCategory.Q.map φ) := by
  have h := Cocycle.fromSingleMk_postcomp f (zero_add n) (n + 1) rfl hf φ
  rw [dm, dm, tr, tr, h, Cocycle.equivHomShift_symm_postcomp, Functor.map_comp]
  have h2 := (DerivedCategory.Q.commShiftIso n).hom.naturality φ
  simp only [Category.assoc]
  congr 2

end Abs

section Site
variable {B : Scheme.{0}} {q : ℕ}

private noncomputable abbrev Z0 (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ (B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q)))

private noncomputable abbrev ZS (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ SShv B q :=
  Z0 B q ⋙ presheafToSheaf (EtTop B) _

private noncomputable def tau (U : B.Etale) : ((Z0 B q).obj U).obj (op U) :=
  ModuleCat.freeMk (ULift.up (𝟙 U))

private lemma tau_map {U U' : B.Etale} (a : U' ⟶ U) :
    ((((Z0 B q).obj U).map a.op).hom (tau U) : ((Z0 B q).obj U).obj (op U')) = ModuleCat.freeMk (ULift.up a) := by
  have h := ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) (uliftFunctor.{1, 0}.map ((yoneda.obj U).map a.op)) (ULift.up (𝟙 U))
  refine h.trans ?_
  congr 1

private lemma nat_ap {M N : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} (η : M ⟶ N) {U U' : B.Etale} (a : U' ⟶ U)
    (x : M.obj (op U)) : (η.app (op U')).hom ((M.map a.op).hom x) = (N.map a.op).hom ((η.app (op U)).hom x) :=
  ConcreteCategory.congr_hom (η.naturality a.op) x

private lemma pre_inj {U : B.Etale} {N : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} {η γ : (Z0 B q).obj U ⟶ N}
    (h : (η.app (op U)).hom (tau U) = (γ.app (op U)).hom (tau U)) : η = γ := by
  apply NatTrans.ext
  funext V
  induction V using Opposite.rec with | _ V => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨k⟩
  have e := tau_map (q := q) (k : V ⟶ U)
  have h1 := nat_ap η (k : V ⟶ U) (tau U)
  have h2 := nat_ap γ (k : V ⟶ U) (tau U)
  rw [e, h] at h1
  rw [e] at h2
  exact h1.trans h2.symm

private noncomputable def pD {U : B.Etale} {N : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} (s : N.obj (op U))
    (V : B.Etaleᵒᵖ) : ((Z0 B q).obj U).obj V ⟶ N.obj V :=
  ModuleCat.freeDesc (↾fun k : ULift.{1} (V.unop ⟶ U) => (N.map k.down.op).hom s)

private lemma pD_mk {U : B.Etale} {N : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} (s : N.obj (op U))
    (V : B.Etaleᵒᵖ) (k : V.unop ⟶ U) :
    (pD s V).hom (ModuleCat.freeMk (ULift.up k) : ((Z0 B q).obj U).obj V) = (N.map k.op).hom s :=
  ModuleCat.freeDesc_apply (↾fun k : ULift.{1} (V.unop ⟶ U) => (N.map k.down.op).hom s) (ULift.up k)

private lemma fm_map {U : B.Etale} {V V' : B.Etaleᵒᵖ} (g : V ⟶ V') (k : V.unop ⟶ U) :
    ((((Z0 B q).obj U).map g).hom (ModuleCat.freeMk (ULift.up k) : ((Z0 B q).obj U).obj V) : ((Z0 B q).obj U).obj V') =
      ModuleCat.freeMk (ULift.up (g.unop ≫ k)) := by
  have h := ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) (uliftFunctor.{1, 0}.map ((yoneda.obj U).map g)) (ULift.up k)
  refine h.trans ?_
  congr 1

private lemma pre_surj {U : B.Etale} {N : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} (s : N.obj (op U)) :
    ∃ η : (Z0 B q).obj U ⟶ N, (η.app (op U)).hom (tau U) = s := by
  refine ⟨{ app := pD s, naturality := ?_ }, ?_⟩
  · intro V V' g
    apply ModuleCat.free_hom_ext
    rintro ⟨k⟩
    have e1 := fm_map (q := q) g (k : V.unop ⟶ U)
    have e2 := pD_mk s V' (g.unop ≫ (k : V.unop ⟶ U))
    have e3 := pD_mk s V (k : V.unop ⟶ U)
    change (pD s V').hom ((((Z0 B q).obj U).map g).hom (ModuleCat.freeMk (ULift.up (k : V.unop ⟶ U)) : ((Z0 B q).obj U).obj V)) =
      (N.map g).hom ((pD s V).hom (ModuleCat.freeMk (ULift.up (k : V.unop ⟶ U)) : ((Z0 B q).obj U).obj V))
    refine (congrArg (fun x => (pD s V').hom x) e1).trans (e2.trans ?_)
    refine Eq.trans ?_ (congrArg (fun x => (N.map g).hom x) e3.symm)
    rw [op_comp, Functor.map_comp]
    rfl
  · change (pD s (op U)).hom (ModuleCat.freeMk (ULift.up (𝟙 U)) : ((Z0 B q).obj U).obj (op U)) = s
    have e := pD_mk s (op U) (𝟙 U)
    refine e.trans ?_
    change (N.map (𝟙 U).op).hom s = s
    simp

private noncomputable def gen (U : B.Etale) : Sc ((ZS B q).obj U) U :=
  ((toSheafify (EtTop B) ((Z0 B q).obj U)).app (op U)).hom (tau U)

private noncomputable def ev (F : SShv B q) (U : B.Etale) (f : (ZS B q).obj U ⟶ F) : Sc F U :=
  (f.hom.app (op U)).hom (gen U)

private lemma ev_eq (F : SShv B q) (U : B.Etale) (f : (ZS B q).obj U ⟶ F) :
    ev F U f = ((((sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv ((Z0 B q).obj U) F f).app (op U)).hom (tau U)) := by
  have e2 := Adjunction.homEquiv_unit (sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))) (X := (Z0 B q).obj U) (Y := F) (f := f)
  exact (congrArg (fun η : (Z0 B q).obj U ⟶ F.obj => (η.app (op U)).hom (tau U)) e2).symm

private lemma ev_bij (F : SShv B q) (U : B.Etale) : Function.Bijective (ev F U) := by
  have hA := ((sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv ((Z0 B q).obj U) F).bijective
  constructor
  · intro f g h
    rw [ev_eq, ev_eq] at h
    exact hA.1 (pre_inj h)
  · intro s
    obtain ⟨η, hη⟩ := pre_surj (N := F.obj) s
    obtain ⟨f, rfl⟩ := hA.2 η
    exact ⟨f, (ev_eq F U f).trans hη⟩

private lemma ev_post {F G : SShv B q} (φ : F ⟶ G) (U : B.Etale) (f : (ZS B q).obj U ⟶ F) :
    ev G U (f ≫ φ) = (φ.hom.app (op U)).hom (ev F U f) := rfl

private lemma ev_sub (F : SShv B q) (U : B.Etale) (f g : (ZS B q).obj U ⟶ F) :
    ev F U (f - g) = ev F U f - ev F U g := rfl

private lemma gen_map {U U' : B.Etale} (a : U' ⟶ U) :
    ((((ZS B q).map a).hom.app (op U')).hom (gen U') : Sc ((ZS B q).obj U) U') =
      ((((ZS B q).obj U).obj.map a.op).hom (gen U)) := by
  have h := toSheafify_naturality (EtTop B) ((Z0 B q).map a)
  have h2 := ConcreteCategory.congr_hom (congrArg (fun t => t.app (op U')) h) (tau U')
  have h3 : (((Z0 B q).map a).app (op U')).hom (tau U') = (((Z0 B q).obj U).map a.op).hom (tau U) := by
    rw [tau_map]
    refine (ModuleCat.free_map_apply (R := ULift.{1} (ZMod q)) (uliftFunctor.{1, 0}.map ((yoneda.map a).app (op U'))) (ULift.up (𝟙 U'))).trans ?_
    congr 1
  have h4 := nat_ap (toSheafify (EtTop B) ((Z0 B q).obj U)) a (tau U)
  exact h2.symm.trans ((congrArg (fun x => ((toSheafify (EtTop B) ((Z0 B q).obj U)).app (op U')).hom x) h3).trans h4)

private lemma ev_pre {F : SShv B q} {U U' : B.Etale} (a : U' ⟶ U) (f : (ZS B q).obj U ⟶ F) :
    ev F U' ((ZS B q).map a ≫ f) = (F.obj.map a.op).hom (ev F U f) := by
  have h := nat_ap f.hom a (gen U)
  refine Eq.trans ?_ h
  exact congrArg (fun x => (f.hom.app (op U')).hom x) (gen_map a)

private noncomputable def ee (F : SShv B q) (U : B.Etale) : Sc F U → ((ZS B q).obj U ⟶ F) :=
  (Equiv.ofBijective _ (ev_bij F U)).symm

private lemma ev_ee (F : SShv B q) (U : B.Etale) (s : Sc F U) : ev F U (ee F U s) = s :=
  (Equiv.ofBijective _ (ev_bij F U)).apply_symm_apply s

private lemma ee_ev (F : SShv B q) (U : B.Etale) (f : (ZS B q).obj U ⟶ F) : ee F U (ev F U f) = f :=
  (Equiv.ofBijective _ (ev_bij F U)).symm_apply_apply f

private lemma ee_post {F G : SShv B q} (φ : F ⟶ G) (U : B.Etale) (s : Sc F U) :
    ee G U ((φ.hom.app (op U)).hom s) = ee F U s ≫ φ := by
  apply (ev_bij G U).1
  rw [ev_ee, ev_post, ev_ee]

private lemma ee_sub (F : SShv B q) (U : B.Etale) (s s' : Sc F U) :
    ee F U (s - s') = ee F U s - ee F U s' := by
  apply (ev_bij F U).1
  rw [ev_ee, ev_sub, ev_ee, ev_ee]

private lemma ee_pre {F : SShv B q} {U U' : B.Etale} (a : U' ⟶ U) (s : Sc F U) :
    ee F U' ((F.obj.map a.op).hom s) = (ZS B q).map a ≫ ee F U s := by
  apply (ev_bij F U').1
  rw [ev_ee, ev_pre, ev_ee]

private lemma ee_zero (F : SShv B q) (U : B.Etale) : ee F U (0 : Sc F U) = 0 := by
  apply (ev_bij F U).1
  rw [ev_ee]
  rfl

private lemma ee_closed {T : CochainComplex (SShv B q) ℤ} {n m : ℤ} {U : B.Etale} {s : Sc (T.X n) U}
    (h : dS T n m U s = 0) : ee (T.X n) U s ≫ T.d n m = 0 := by
  rw [← ee_post]
  change ee (T.X m) U (dS T n m U s) = 0
  rw [h, ee_zero]

end Site

end UpperTheory.YonedaTruncation

open UpperTheory.YonedaTruncation in
theorem UpperTheory.ext_free_etale_sheaf_yoneda :
    ∀ (B : Scheme.{0}) (q : ℕ), Yon B q := by
  intro B q
  refine ⟨fun T U n s hs => dm ((ZS B q).obj U) T n (ee (T.X n) U s) (ee_closed hs), ?_, ?_, ?_, ?_⟩
  · rintro T U n s hs s' hs' ⟨b, hb⟩
    refine dm_eq _ _ ⟨ee (T.X (n - 1)) U b, ?_⟩
    rw [← ee_post, ← ee_sub]
    exact congrArg (ee (T.X n) U) hb
  · intro T hT U n
    refine ⟨fun s hs s' hs' h => ?_, fun x => ?_⟩
    · obtain ⟨g, hg⟩ := dm_inj _ _ h
      refine ⟨ev _ U g, ?_⟩
      apply (Equiv.ofBijective _ (ev_bij (T.X n) U)).symm.injective
      change ee (T.X n) U (((T.d (n - 1) n).hom.app (op U)).hom (ev _ U g)) = ee (T.X n) U (s - s')
      rw [ee_post, ee_ev, ee_sub, hg]
    · obtain ⟨f, hf, h⟩ := dm_surj (A := (ZS B q).obj U) (T := T) (n := n) x
      refine ⟨ev _ U f, ?_, ?_⟩
      · change ev _ U (f ≫ T.d n (n + 1)) = 0
        rw [hf]
        rfl
      · exact (dm_congr _ _ (ee_ev _ U f)).trans h
  · intro T U U' a n s hs hs'
    have hc : ((ZS B q).map a ≫ ee (T.X n) U s) ≫ T.d n (n + 1) = 0 := by
      rw [Category.assoc, ee_closed hs, comp_zero]
    exact (dm_congr _ hc (ee_pre a s)).trans (dm_pre ((ZS B q).map a) _ (ee_closed hs) hc)
  · intro T T' φ U n s hs hs'
    have hc : (ee (T.X n) U s ≫ φ.f n) ≫ T'.d n (n + 1) = 0 := by
      rw [Category.assoc, φ.comm, ← Category.assoc, ee_closed hs, zero_comp]
    exact (dm_congr _ hc (ee_post (φ.f n) U s)).trans (dm_post φ _ (ee_closed hs) hc)
