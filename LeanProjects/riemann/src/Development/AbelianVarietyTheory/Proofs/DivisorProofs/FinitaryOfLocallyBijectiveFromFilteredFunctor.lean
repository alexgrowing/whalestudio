import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoverModelOfIsColimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffEl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsColimitPushoutUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafSectionEqZeroAtStageOfFilteredColimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FinitaryOfLocBij

variable {R : Type} [CommRing R]

lemma etale_inr {A B C P : CommRingCat.{0}} {g : A ⟶ B} {f : A ⟶ C} {inl : B ⟶ P}
    {inr : C ⟶ P} (sq : IsPushout g f inl inr) (hg : g.hom.Etale) : inr.hom.Etale := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty @RingHom.Etale) sq.flip hg

lemma cover_inr {ι : Type} {A C : CommRingCat.{0}} {B P : ι → CommRingCat.{0}}
    (g : ∀ i, A ⟶ B i) (f : A ⟶ C) (inl : ∀ i, B i ⟶ P i) (inr : ∀ i, C ⟶ P i)
    (sq : ∀ i, IsPushout (g i) f (inl i) (inr i))
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) :
    ∀ p : Spec C, ∃ i v, Spec.map (inr i) v = p := by
  intro p
  obtain ⟨i, v, hv⟩ := hcov (Spec.map f p)
  obtain ⟨z, hz⟩ := GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (sq i).flip p v hv.symm
  exact ⟨i, z, hz⟩

lemma eta_map {M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)} {F : Shv R}
    (η : M ⟶ onRings F) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : M.obj A) :
    ((onRings F).map f).hom ((η.app A).hom x) = (η.app B).hom ((M.map f).hom x) := by
  change (η.app A ≫ (onRings F).map f).hom x = (M.map f ≫ η.app B).hom x
  rw [η.naturality]

lemma map_comp_apply (N : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {A B C : CommRingCat.{0}}
    (f : A ⟶ B) (g : B ⟶ C) (x : N.obj A) :
    (N.map (f ≫ g)).hom x = (N.map g).hom ((N.map f).hom x) := by
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

lemma isPushout_pushouts {C : Type*} [Category C] {A C₁ C₂ X B₁ B₂ P Q : C} {u₁ : A ⟶ C₁}
    {u₂ : A ⟶ C₂} {f : A ⟶ X} {i₁ : C₁ ⟶ B₁} {g₁ : X ⟶ B₁} {i₂ : C₂ ⟶ B₂} {g₂ : X ⟶ B₂}
    {p₁ : C₁ ⟶ P} {p₂ : C₂ ⟶ P} {q₁ : B₁ ⟶ Q} {q₂ : B₂ ⟶ Q} {w : P ⟶ Q}
    (h₁ : IsPushout u₁ f i₁ g₁) (h₂ : IsPushout u₂ f i₂ g₂) (hP : IsPushout u₁ u₂ p₁ p₂)
    (hQ : IsPushout g₁ g₂ q₁ q₂) (e₁ : p₁ ≫ w = i₁ ≫ q₁) (e₂ : p₂ ≫ w = i₂ ≫ q₂) :
    IsPushout (u₁ ≫ p₁) f w (g₁ ≫ q₁) := by
  have s : IsPushout u₂ (u₁ ≫ i₁) (p₂ ≫ w) q₁ := by
    rw [h₁.w, e₂]; exact h₂.paste_vert hQ.flip
  have t : IsPushout p₁ i₁ w q₁ := IsPushout.of_top s e₁ hP.flip
  exact h₁.paste_horiz t

lemma glue (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {C : ι → CommRingCat.{0}}
    (e : ∀ i, A ⟶ C i) (he : ∀ i, (e i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (e i) v = p) (s : ∀ i, (onRings F).obj (C i))
    (hs : ∀ a b, ((onRings F).map (pushout.inl (e a) (e b))).hom (s a) =
      ((onRings F).map (pushout.inr (e a) (e b))).hom (s b)) :
    ∃ y : (onRings F).obj A, ∀ i, ((onRings F).map (e i)).hom y = s i := by
  refine (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (C i)) (fun i => Spec.map (e i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (he i)) hcov).2 s ?_
  intro a b
  have H := isPullback_SpecMap_pushout (e a) (e b)
  have h1 : pullback.fst (Spec.map (e a)) (Spec.map (e b)) =
      H.isoPullback.inv ≫ Spec.map (pushout.inl (e a) (e b)) := by simp
  have h2 : pullback.snd (Spec.map (e a)) (Spec.map (e b)) =
      H.isoPullback.inv ≫ Spec.map (pushout.inr (e a) (e b)) := by simp
  have := congrArg (fun z => (F.obj.map H.isoPullback.inv.op).hom z) (hs a b)
  simp only [Sec.res, h1, h2, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact this

lemma sep (F : Shv R) {ι : Type} {A : CommRingCat.{0}} {C : ι → CommRingCat.{0}}
    (e : ∀ i, A ⟶ C i) (he : ∀ i, (e i).hom.Etale)
    (hcov : ∀ p : Spec A, ∃ i v, Spec.map (e i) v = p) (y z : (onRings F).obj A)
    (h : ∀ i, ((onRings F).map (e i)).hom y = ((onRings F).map (e i)).hom z) : y = z := by
  rw [← sub_eq_zero]
  refine (GlobalTheory.EtC.sec_sep_glue_of_points R F (Spec A) ι (fun i => Spec (C i)) (fun i => Spec.map (e i))
    (fun i => (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (he i)) hcov).1 _ ?_
  intro i
  change ((onRings F).map (e i)).hom (y - z) = 0
  rw [map_sub, h i, sub_self]

end GlobalTheory.EtC.FinitaryOfLocBij

namespace GlobalTheory.EtC.FinitaryOfLocBij

variable {R : Type} [CommRing R]

lemma cocone_nat {C : Type} [Category C] {D' : C ⥤ CommRingCat.{0}} {B : CommRingCat.{0}}
    (ιB : D' ⟶ (Functor.const C).obj B) {K K' : C} (φ : K ⟶ K') :
    D'.map φ ≫ ιB.app K' = ιB.app K := by
  simpa using ιB.naturality φ

lemma po_stage {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {j : J} {B' : CommRingCat.{0}}
    {g' : D.obj j ⟶ B'} {D' : Under j ⥤ CommRingCat.{0}} {u : Under.forget j ⋙ D ⟶ D'}
    {v : (Functor.const _).obj B' ⟶ D'} (hpo : ∀ k, IsPushout g' (D.map k.hom) (v.app k) (u.app k))
    {K K' : Under j} (φ : K ⟶ K') :
    IsPushout (u.app K) (D.map φ.right) (D'.map φ) (u.app K') := by
  have hv : v.app K ≫ D'.map φ = v.app K' := by simpa using (v.naturality φ).symm
  have e1 : D.map K.hom ≫ D.map φ.right = D.map K'.hom := by rw [← Functor.map_comp, Under.w φ]
  have s : IsPushout g' (D.map K.hom ≫ D.map φ.right) (v.app K ≫ D'.map φ) (u.app K') := by
    rw [e1, hv]; exact hpo K'
  exact IsPushout.of_top s (u.naturality φ).symm (hpo K)

lemma po_colim {J : Type} [SmallCategory J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D} {j : J}
    {B' B : CommRingCat.{0}} {g' : D.obj j ⟶ B'} {h : B' ⟶ B} {g : c.pt ⟶ B}
    (hbig : IsPushout g' (c.ι.app j) h g) {D' : Under j ⥤ CommRingCat.{0}}
    {ιB : D' ⟶ (Functor.const _).obj B} {u : Under.forget j ⋙ D ⟶ D'}
    {v : (Functor.const _).obj B' ⟶ D'} (k : Under j)
    (hk : IsPushout g' (D.map k.hom) (v.app k) (u.app k) ∧ v.app k ≫ ιB.app k = h ∧
      u.app k ≫ ιB.app k = c.ι.app k.right ≫ g) :
    IsPushout (u.app k) (c.ι.app k.right) (ιB.app k) g := by
  have e1 : D.map k.hom ≫ c.ι.app k.right = c.ι.app j := c.w k.hom
  rw [← e1, ← hk.2.1] at hbig
  exact IsPushout.of_top hbig hk.2.2 hk.1

theorem surj (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F)
    (hM : PreservesFilteredColimitsOfSize.{0, 0} M)
    (hloc : ∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x)
    (hinj : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), ((onRings F).map (D.map f)).hom y = 0)
    (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (x : (onRings F).obj c.pt) :
    ∃ (j : J) (y : (onRings F).obj (D.obj j)), ((onRings F).map (c.ι.app j)).hom y = x := by
  classical
  obtain ⟨ι, _, B, g, m, hg, hcov, hm⟩ := hloc _ x
  have hMel := (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ M).2.1 hM
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨j, -, B', g', h, hsq, hcov'⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc ι B g hg hcov j0
  choose D' ιB u v hcol hpush using fun i =>
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc j (B' i) (B i) (g' i) (h i) (g i)
      (hsq i).2
  have hlift : ∀ i, ∃ k : Under j, ∃ n : M.obj ((D' i).obj k), (M.map ((ιB i).app k)).hom n = m i :=
    fun i => (hMel (Under j) (D' i) _ (hcol i).some).1 (m i)
  choose k n hn using hlift
  letI := Fintype.ofFinite ι
  obtain ⟨K, hK⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  have e : ∀ i, k i ⟶ K := fun i => (hK (Finset.mem_image_of_mem _ (Finset.mem_univ i))).some
  let s : ∀ i, (onRings F).obj ((D' i).obj K) :=
    fun i => (η.app _).hom ((M.map ((D' i).map (e i))).hom (n i))
  have hs : ∀ i, ((onRings F).map ((ιB i).app K)).hom (s i) = ((onRings F).map (g i)).hom x := by
    intro i
    simp only [s]
    rw [eta_map, ← map_comp_apply, cocone_nat, hn]
    exact hm i
  let Kp : Under K.right → Under j := fun L => Under.mk (K.hom ≫ L.hom)
  let φ : ∀ L : Under K.right, K ⟶ Kp L := fun L => Under.homMk L.hom
  let s' : ∀ (L : Under K.right) i, (onRings F).obj ((D' i).obj (Kp L)) :=
    fun L i => ((onRings F).map ((D' i).map (φ L))).hom (s i)
  have hover : ∀ a b : ι, ∃ L0 : Under K.right, ∀ (L : Under K.right) (_ : L0 ⟶ L),
      ((onRings F).map (pushout.inl ((u a).app (Kp L)) ((u b).app (Kp L)))).hom (s' L a) =
      ((onRings F).map (pushout.inr ((u a).app (Kp L)) ((u b).app (Kp L)))).hom (s' L b) := by
    intro a b
    let w : pushout ((u a).app K) ((u b).app K) ⟶ pushout (g a) (g b) :=
      pushout.desc ((ιB a).app K ≫ pushout.inl (g a) (g b)) ((ιB b).app K ≫ pushout.inr (g a) (g b))
        (by
          have hua : ∀ i, (u i).app K ≫ (ιB i).app K = c.ι.app K.right ≫ g i := fun i => (hpush i K).2.2
          rw [reassoc_of% (hua a), reassoc_of% (hua b)]
          exact (Category.assoc _ _ _).trans ((c.ι.app K.right ≫= pushout.condition).trans
            (Category.assoc _ _ _).symm))
    let t : (onRings F).obj (pushout ((u a).app K) ((u b).app K)) :=
      ((onRings F).map (pushout.inl _ _)).hom (s a) - ((onRings F).map (pushout.inr _ _)).hom (s b)
    have ht : ((onRings F).map w).hom t = 0 := by
      simp only [t, map_sub, ← map_comp_apply, w, pushout.inl_desc, pushout.inr_desc]
      rw [map_comp_apply _ ((ιB a).app K), map_comp_apply _ ((ιB b).app K), hs, hs,
        ← map_comp_apply, ← map_comp_apply, pushout.condition, sub_self]
    have hPO : IsPushout ((u a).app K ≫ pushout.inl _ _) (c.ι.app K.right) w
        (g a ≫ pushout.inl (g a) (g b)) :=
      isPushout_pushouts (po_colim (hsq a).2 K (hpush a K)) (po_colim (hsq b).2 K (hpush b K))
        (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _) (pushout.inl_desc _ _ _)
        (pushout.inr_desc _ _ _)
    obtain ⟨D'', ι'', u'', v'', hcol'', hpush''⟩ :=
      GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J D c hc K.right _ _ _ w _ hPO
    let k0 : Under K.right := Under.mk (𝟙 _)
    have h0 : ((onRings F).map (ι''.app k0)).hom (((onRings F).map (v''.app k0)).hom t) = 0 := by
      rw [← map_comp_apply, (hpush'' k0).2.1, ht]
    obtain ⟨L0, f, hf⟩ := hinj (Under K.right) D'' _ hcol''.some k0 _ h0
    refine ⟨L0, fun L ψ => ?_⟩
    have hvL : ((onRings F).map (v''.app L)).hom t = 0 := by
      have e1 : v''.app k0 ≫ D''.map f ≫ D''.map ψ = v''.app L := by
        rw [← D''.map_comp]
        simpa using (v''.naturality (f ≫ ψ)).symm
      rw [← e1, map_comp_apply, map_comp_apply, hf, map_zero]
    let w' : pushout ((u a).app K) ((u b).app K) ⟶ pushout ((u a).app (Kp L)) ((u b).app (Kp L)) :=
      pushout.desc ((D' a).map (φ L) ≫ pushout.inl _ _) ((D' b).map (φ L) ≫ pushout.inr _ _)
        (by
          rw [← Category.assoc, ← Category.assoc, ← (u a).naturality, ← (u b).naturality]
          simp only [Category.assoc, pushout.condition])
    have hPO' : IsPushout ((u a).app K ≫ pushout.inl _ _) (D.map L.hom) w'
        ((u a).app (Kp L) ≫ pushout.inl _ _) :=
      isPushout_pushouts (po_stage (fun k => (hpush a k).1) (φ L))
        (po_stage (fun k => (hpush b k).1) (φ L))
        (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _) (pushout.inl_desc _ _ _)
        (pushout.inr_desc _ _ _)
    have hw' : v''.app L ≫ ((hpush'' L).1.isoIsPushout _ _ hPO').hom = w' :=
      IsPushout.inl_isoIsPushout_hom _ _ (hpush'' L).1 hPO'
    have hwt : ((onRings F).map w').hom t = 0 := by
      rw [← hw', map_comp_apply, hvL, map_zero]
    simp only [t, map_sub, sub_eq_zero, ← map_comp_apply, w', pushout.inl_desc,
      pushout.inr_desc] at hwt
    simpa only [s', ← map_comp_apply] using hwt
  choose L0 hL0 using hover
  obtain ⟨Lc, hLc⟩ := IsFiltered.sup_objs_exists (Finset.univ.image (fun p : ι × ι => L0 p.1 p.2))
  have ψ : ∀ a b, L0 a b ⟶ Lc := fun a b =>
    (hLc (Finset.mem_image_of_mem (fun p : ι × ι => L0 p.1 p.2) (Finset.mem_univ (a, b)))).some
  let e' : ∀ i, D.obj Lc.right ⟶ (D' i).obj (Kp Lc) := fun i => (u i).app (Kp Lc)
  obtain ⟨y, hy⟩ := glue F e'
    (fun i => etale_inr (hpush i (Kp Lc)).1 (hsq i).1)
    (cover_inr g' (D.map (Kp Lc).hom) (fun i => (v i).app (Kp Lc)) e'
      (fun i => (hpush i _).1) hcov')
    (s' Lc) (fun a b => hL0 a b Lc (ψ a b))
  refine ⟨Lc.right, y, ?_⟩
  apply sep F g hg hcov
  intro i
  have hu : e' i ≫ (ιB i).app (Kp Lc) = c.ι.app Lc.right ≫ g i := (hpush i _).2.2
  rw [← map_comp_apply, ← hu, map_comp_apply, hy i]
  simp only [s']
  rw [← map_comp_apply, cocone_nat, hs]

end GlobalTheory.EtC.FinitaryOfLocBij

namespace GlobalTheory.EtC.FinitaryOfLocBij

theorem finitary_of_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (F : Shv R) (η : M ⟶ onRings F), PreservesFilteredColimitsOfSize.{0, 0} M → (∀ (A : CommRingCat.{0}) (x : (onRings F).obj A), ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i) (m : ∀ i, M.obj (B i)), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (η.app (B i)).hom (m i) = ((onRings F).map (g i)).hom x) → (∀ (A : CommRingCat.{0}) (m : M.obj A), (η.app A).hom m = 0 → ∃ (ι : Type) (_ : Finite ι) (B : ι → CommRingCat.{0}) (g : ∀ i, A ⟶ B i), (∀ i, (g i).hom.Etale) ∧ (∀ p : Spec A, ∃ i v, Spec.map (g i) v = p) ∧ ∀ i, (M.map (g i)).hom m = 0) → Finitary F := by
  intro R _ M F η hM hloc hker
  have hinj := GlobalTheory.T.sheafSection_eq_zero_at_stage_of_filtered_colimit R M F η hM hloc hker
  show PreservesFilteredColimitsOfSize.{0, 0} (onRings F)
  refine (GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements _ (onRings F)).2.2 ?_
  intro J _ _ D c hc
  exact ⟨surj M F η hM hloc hinj J D c hc, hinj J D c hc⟩

end GlobalTheory.EtC.FinitaryOfLocBij
