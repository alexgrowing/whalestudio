import Development.EtaleCohomology.EtaleSheaves.KummerSequence.KummerH0Surjection

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.KummerH0Surjection
open CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafKumFieldPf.H0Naturality

set_option backward.isDefEq.respectTransparency false in
theorem resι_nat {F G : Shv ℤ} (φ : F ⟶ G) : resι ℤ F ≫ (resMap ℤ φ).f 0 = φ ≫ resι ℤ G := by
  have h := congrArg (fun f => HomologicalComplex.Hom.f f 0)
    (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))
  simp only [HomologicalComplex.comp_f] at h
  simp only [resι, resMap, InjectiveResolution.ι'_f_zero, InjectiveResolution.cochainComplexXIso]
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by rfl)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h]
  first | rfl | simp | (congr 1)

theorem free_ext (X : Scheme.{0}) {I : Shv ℤ}
    (f g : (free ℤ).obj ((sch.obj X).obj (op (SimplexCategory.mk 0))) ⟶ I)
    (h : (f.hom.app (op X)).hom (freeGen ℤ _ X (𝟙 X)) = (g.hom.app (op X)).hom (freeGen ℤ _ X (𝟙 X))) : f = g := by
  have key : ∀ (η : (freeP ℤ).obj ((sch.obj X).obj (op (SimplexCategory.mk 0))) ⟶ I.obj) (U : Scheme.{0}) (x : U ⟶ X),
      (η.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) =
        (I.obj.map x.op).hom ((η.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) := by
    intro η U x
    have := congrArg (fun m => m.hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) (η.naturality x.op)
    refine Eq.trans ?_ this
    rw [ModuleCat.hom_comp]
    erw [LinearMap.comp_apply]
    congr 1
    erw [ModuleCat.free_map_apply]
    congr 2
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ I.2
  refine NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun ⟨x⟩ => ?_)
  have h1 := key (toSheafify _ _ ≫ f.hom) U.unop x
  have h2 := key (toSheafify _ _ ≫ g.hom) U.unop x
  refine h1.trans (h2.trans ?_).symm
  congr 1
  exact h.symm

theorem coc_ext (X : Scheme.{0}) (G : Shv ℤ) (a b : Cocycle ((chains ℤ).obj (sch.obj X)) (res ℤ G) 0)
    (h : ev a.1 0 0 (by simp) X (𝟙 X) = ev b.1 0 0 (by simp) X (𝟙 X)) : a = b := by
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  obtain rfl : p = q := by omega
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by show ((i:ℕ):ℤ) ≠ p; omega)
  · have e := free_ext X ((chainsXIso ℤ (sch.obj X) 0).inv ≫ a.1.v 0 0 (by simp))
      ((chainsXIso ℤ (sch.obj X) 0).inv ≫ b.1.v 0 0 (by simp)) h
    have := congrArg ((chainsXIso ℤ (sch.obj X) 0).hom ≫ ·) e
    simpa using this
  · apply IsZero.eq_of_src
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by show -((i:ℕ):ℤ) ≠ p; omega)

theorem ev_post (X : Scheme.{0}) {F G : Shv ℤ} (φ : F ⟶ G) (α : Cocycle ((chains ℤ).obj (sch.obj X)) (res ℤ F) 0) :
    ev (zcomp α (Cocycle.ofHom (resMap ℤ φ)) (add_zero 0)).1 0 0 (by simp) X (𝟙 X) =
      (((resMap ℤ φ).f 0).hom.app (op X)).hom (ev α.1 0 0 (by simp) X (𝟙 X)) := by
  simp only [ev, zcomp, Cocycle.mk, Cochain.comp_zero_cochain_v, Cocycle.ofHom, Cochain.ofHom_v]
  rfl

theorem etale_degree_zero_cohomology_natural_in_sheaf (hA9 : A9) : EtaleDegreeZeroCohomologyNaturallyIsoToSections := by
  intro _
  choose e he using fun F : Shv ℤ => (hA9 ℤ F).2
  refine ⟨e, ?_⟩
  intro F G φ X s
  obtain ⟨α, hα, hαv⟩ := (he F).2 X s
  obtain ⟨β, hβ, hβv⟩ := (he G).2 X (Sec.map φ s)
  rw [← hα, ← hβ]
  show CohomologyClass.mk (zcomp α (Cocycle.ofHom (resMap ℤ φ)) (add_zero 0)) = _
  congr 1
  apply coc_ext
  rw [hβv, ev_post, hαv]
  have := congrArg (fun m => (m.hom.app (op X)).hom s) (resι_nat φ)
  exact this
