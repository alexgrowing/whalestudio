import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoverModelOfIsColimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffEl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsColimitPushoutUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamily
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FilteredSections

variable {R : Type} [CommRing R]

lemma etale_of_isPushout {A B C P : CommRingCat.{0}} {g : A ⟶ B} {f : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (sq : IsPushout g f inl inr) (hg : g.hom.Etale) : inr.hom.Etale := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty @RingHom.Etale) sq.flip hg

lemma cover_of_isPushout {ι : Type} {A C : CommRingCat.{0}} {B P : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (f : A ⟶ C) (inl : ∀ i, B i ⟶ P i) (inr : ∀ i, C ⟶ P i)
    (sq : ∀ i, IsPushout (g i) f (inl i) (inr i))
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) :
    ∀ p : Spec C, ∃ i v, Spec.map (inr i) v = p := by
  intro p
  obtain ⟨i, v, hv⟩ := hcov (Spec.map f p)
  obtain ⟨z, hz⟩ := GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (sq i).flip p v hv.symm
  exact ⟨i, z, hz⟩

lemma eq_zero_of_cover (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {B : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (hg : ∀ i, (g i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) (y : (onRings F).obj A)
    (hy : ∀ i, ((onRings F).map (g i)).hom y = 0) : y = 0 :=
  (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (B i)) (fun i => Spec.map (g i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (hg i)) hcov).1 y hy

lemma map_eta {M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)} {F : Shv R}
    (η : M ⟶ onRings F) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : M.obj A) :
    ((onRings F).map f).hom ((η.app A).hom x) = (η.app B).hom ((M.map f).hom x) := by
  change (η.app A ≫ (onRings F).map f).hom x = (M.map f ≫ η.app B).hom x
  rw [η.naturality]

lemma stage_of_pieces (F : Shv R) {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (j : J) (y : (onRings F).obj (D.obj j)) {ι : Type} [Finite ι]
    (B : ι → CommRingCat.{0}) (g : ∀ i, D.obj j ⟶ B i) (hg : ∀ i, (g i).hom.Etale)
    (hcov : ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g i) v = p)
    (D' : ι → (Under j ⥤ CommRingCat.{0})) (u : ∀ i, Under.forget j ⋙ D ⟶ D' i)
    (v : ∀ i, (Functor.const _).obj (B i) ⟶ D' i)
    (sq : ∀ i (k : Under j), IsPushout (g i) (D.map k.hom) ((v i).app k) ((u i).app k))
    (hk : ∀ i, ∃ k : Under j,
      ((onRings F).map ((v i).app k)).hom (((onRings F).map (g i)).hom y) = 0) :
    ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  classical
  choose k hk using hk
  letI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  have e : ∀ i, k i ⟶ K := fun i => (hK (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  refine ⟨K.right, K.hom, ?_⟩
  apply eq_zero_of_cover F (fun i => (u i).app K) (fun i => etale_of_isPushout (sq i K) (hg i))
    (cover_of_isPushout g (D.map K.hom) (fun i => (v i).app K) (fun i => (u i).app K)
      (fun i => sq i K) hcov)
  intro i
  have h1 : (v i).app (k i) ≫ (D' i).map (e i) = (v i).app K := by
    simpa using ((v i).naturality (e i)).symm
  have h2 : D.map K.hom ≫ (u i).app K = g i ≫ (v i).app K := (sq i K).w.symm
  have h3 : ((onRings F).map ((u i).app K)).hom (((onRings F).map (D.map K.hom)).hom y) =
      ((onRings F).map ((D' i).map (e i))).hom
        (((onRings F).map ((v i).app (k i))).hom (((onRings F).map (g i)).hom y)) := by
    have := congrArg (fun φ => ((onRings F).map φ).hom y) h2
    rw [← h1] at this
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
    erw [Functor.map_comp (onRings F) (D.map K.hom) ((u i).app K)] at this
    exact this
  rw [h3, hk i, map_zero]

lemma stage_of_eta (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R)
    (η : M ⟶ onRings F) (hM : PreservesFilteredColimitsOfSize.{0, 0} M)
    (hker : ∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι)
      (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧
      (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0)
    (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (j : J) (m : M.obj (D.obj j))
    (hm : ((onRings F).map (c.ι.app j)).hom ((η.app _).hom m) = 0) :
    ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom ((η.app _).hom m) = 0 := by
  have hMel := (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ M).2.1 hM
  rw [map_eta] at hm
  obtain ⟨ι, _, B, g, hg, hcov, hz⟩ := hker _ _ hm
  obtain ⟨j', f0, B', g', h, hsq, hcov'⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc ι B g hg hcov j
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j' (B' i) (B i) (g' i) (h i) (g i)
      (hsq i).2
  have hk : ∀ i, ∃ k : Under j', ((onRings F).map ((v i).app k)).hom
      (((onRings F).map (g' i)).hom ((η.app _).hom ((M.map (D.map f0)).hom m))) = 0 := by
    intro i
    let k0 : Under j' := Under.mk (𝟙 j')
    have e1 : D.map f0 ≫ g' i ≫ (v i).app k0 ≫ (ιB i).app k0 = c.ι.app j ≫ g i := by
      rw [(hpush i k0).2.1, (hsq i).2.w, ← Category.assoc, c.w]
    have hdie : (M.map ((ιB i).app k0)).hom ((M.map ((v i).app k0)).hom
        ((M.map (g' i)).hom ((M.map (D.map f0)).hom m))) = 0 := by
      have := congrArg (fun φ => (M.map φ).hom m) e1
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this]
      exact hz i
    obtain ⟨k, f, hf⟩ := (hMel (Under j') (D' i) _ (hcol i).some).2 k0 _ hdie
    refine ⟨k, ?_⟩
    have e2 : (v i).app k0 ≫ (D' i).map f = (v i).app k := by
      simpa using ((v i).naturality f).symm
    rw [map_eta]
    erw [map_eta]
    rw [← e2, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hf,
      map_zero]
  obtain ⟨k, f, hf⟩ := stage_of_pieces F D j' ((η.app _).hom ((M.map (D.map f0)).hom m)) B' g'
    (fun i => (hsq i).1) hcov' D' u v (fun i k => (hpush i k).1) hk
  refine ⟨k, f0 ≫ f, ?_⟩
  rw [map_eta] at hf ⊢
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact hf

theorem eq_zero_at_stage_of_map_colimit_eq_zero : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0 := by
  intro R _ M F η hM hloc hker J _ _ D c hc j y hy
  obtain ⟨ι, _, B, g, m, hg, hcov, hm⟩ := hloc _ y
  have hP : ∀ i, IsPushout (g i) (c.ι.app j) (pushout.inl (g i) (c.ι.app j))
      (pushout.inr (g i) (c.ι.app j)) := fun i => IsPushout.of_hasPushout _ _
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j (B i)
      (pushout (g i) (c.ι.app j)) (g i) (pushout.inl (g i) (c.ι.app j))
      (pushout.inr (g i) (c.ι.app j)) (hP i)
  have hk : ∀ i, ∃ k : Under j,
      ((onRings F).map ((v i).app k)).hom (((onRings F).map (g i)).hom y) = 0 := by
    intro i
    let k0 : Under j := Under.mk (𝟙 j)
    have h0 : ((onRings F).map ((ιB i).app k0)).hom
        ((η.app _).hom ((M.map ((v i).app k0)).hom (m i))) = 0 := by
      calc ((onRings F).map ((ιB i).app k0)).hom ((η.app _).hom ((M.map ((v i).app k0)).hom (m i)))
          = (η.app _).hom ((M.map ((v i).app k0 ≫ (ιB i).app k0)).hom (m i)) := by
            rw [map_eta, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
        _ = ((onRings F).map (pushout.inl (g i) (c.ι.app j))).hom ((η.app _).hom (m i)) := by
            rw [(hpush i k0).2.1, map_eta]
            rfl
        _ = ((onRings F).map (g i ≫ pushout.inl (g i) (c.ι.app j))).hom y := by
            rw [hm i, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
        _ = 0 := by
            rw [pushout.condition, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hy,
              map_zero]
    obtain ⟨k, f, hf⟩ := stage_of_eta M F η hM hker (Under j) (D' i) _ (hcol i).some k0 _ h0
    refine ⟨k, ?_⟩
    have e2 : (v i).app k0 ≫ (D' i).map f = (v i).app k := by
      simpa using ((v i).naturality f).symm
    rw [← hm i]
    erw [map_eta]
    rw [← e2, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      ← map_eta]
    exact hf
  exact stage_of_pieces F D j y B g hg hcov D' u v (fun i k => (hpush i k).1) hk

end GlobalTheory.EtC.FilteredSections
