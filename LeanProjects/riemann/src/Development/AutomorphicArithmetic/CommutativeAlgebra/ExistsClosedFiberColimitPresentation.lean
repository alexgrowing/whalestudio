import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafVanBStalkPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVanBPf LateralTheory.E.LeafVanBStalkPf

namespace UpperTheory.PushoutColimitSpec

private theorem epi_of_closed {R S : CommRingCat.{0}} (q : R ⟶ S) [IsClosedImmersion (Spec.map q)] : Epi q :=
  ⟨fun a b h => Spec.map_injective ((cancel_mono (Spec.map q)).1 (by
    rw [← Spec.map_comp, ← Spec.map_comp, h]))⟩

private theorem isPushout_of_Spec {A B C P : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (inl : B ⟶ P) (inr : C ⟶ P)
    (h : IsPullback (Spec.map inl) (Spec.map inr) (Spec.map f) (Spec.map g)) : IsPushout f g inl inr := by
  have hw : f ≫ inl = g ≫ inr := Spec.map_injective (by simpa using h.w)
  have h' : IsPullback inl.op inr.op f.op g.op :=
    IsPullback.of_map Scheme.Spec (by rw [← op_comp, ← op_comp, hw]) h
  exact h'.unop.flip

private def colimOfPushout {J : Type} [SmallCategory J] {D D' : J ⥤ CommRingCat.{0}} {c : Cocone D} (hc : IsColimit c)
    (c' : Cocone D') (q : ∀ j, D.obj j ⟶ D'.obj j)
    (hq : ∀ {j j' : J} (g : j ⟶ j'), D.map g ≫ q j' = q j ≫ D'.map g) (hepi : ∀ j, Epi (q j))
    (qi : c.pt ⟶ c'.pt) (hqi : ∀ j, c.ι.app j ≫ qi = q j ≫ c'.ι.app j) (j0 : J)
    (hp : IsPushout (c.ι.app j0) (q j0) qi (c'.ι.app j0)) : IsColimit c' :=
  let f (s : Cocone D') : c.pt ⟶ s.pt := hc.desc
    ⟨s.pt, { app := fun j => q j ≫ s.ι.app j
             naturality := fun j j' g => by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
               rw [← Category.assoc, hq, Category.assoc, s.w] }⟩
  have hf (s : Cocone D') (j : J) : c.ι.app j ≫ f s = q j ≫ s.ι.app j := hc.fac _ j
  { desc := fun s => hp.desc (f s) (s.ι.app j0) (hf s j0)
    fac := fun s j => by
      have := hepi j
      rw [← cancel_epi (q j), ← Category.assoc, ← hqi, Category.assoc, hp.inl_desc, hf]
    uniq := fun s m hm => by
      apply hp.hom_ext
      · rw [hp.inl_desc]
        apply hc.hom_ext
        intro j
        rw [← Category.assoc, hqi, Category.assoc, hm, hf]
      · rw [hp.inr_desc, hm] }

private theorem ring_system {J : Type} [SmallCategory J] (Z : J → Scheme.{0}) [∀ j, IsAffine (Z j)]
    (r : ∀ {j j' : J} (_ : j ⟶ j'), Z j' ⟶ Z j) (hid : ∀ j, r (𝟙 j) = 𝟙 _)
    (hcomp : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j''), r (g ≫ g') = r g' ≫ r g) :
    ∃ (D' : J ⥤ CommRingCat.{0}) (ez : ∀ j, Z j ≅ Spec (D'.obj j)),
      ∀ {j j' : J} (g : j ⟶ j'), (ez j').inv ≫ r g ≫ (ez j).hom = Spec.map (D'.map g) := by
  refine ⟨{ obj := fun j => Γ(Z j, ⊤)
            map := fun {j j'} g => Spec.preimage ((Z j').isoSpec.inv ≫ r g ≫ (Z j).isoSpec.hom)
            map_id := fun j => Spec.map_injective (by simp [hid])
            map_comp := fun {j j' j''} g g' => Spec.map_injective (by simp [hcomp]) },
    fun j => (Z j).isoSpec, fun {j j'} g => ?_⟩
  simp

private theorem cocone_system {J : Type} [SmallCategory J] [Nonempty J] (Z : J → Scheme.{0})
    (r : ∀ {j j' : J} (_ : j ⟶ j'), Z j' ⟶ Z j) (D D' : J ⥤ CommRingCat.{0})
    (ez : ∀ j, Z j ≅ Spec (D'.obj j))
    (hr : ∀ {j j' : J} (g : j ⟶ j'), (ez j').inv ≫ r g ≫ (ez j).hom = Spec.map (D'.map g))
    (c : Cocone D) (hc : IsColimit c) (φ : ∀ j, Z j ⟶ Spec (D.obj j)) [∀ j, IsClosedImmersion (φ j)]
    (hφ : ∀ {j j' : J} (g : j ⟶ j'), r g ≫ φ j = φ j' ≫ Spec.map (D.map g))
    (Zi : Scheme.{0}) [IsAffine Zi] (φi : Zi ⟶ Spec c.pt) (l : ∀ j, Zi ⟶ Z j)
    (hl : ∀ {j j' : J} (g : j ⟶ j'), l j' ≫ r g = l j)
    (hlφ : ∀ j, l j ≫ φ j = φi ≫ Spec.map (c.ι.app j))
    (hpb : ∀ j, IsPullback (l j) φi (φ j) (Spec.map (c.ι.app j))) :
    ∃ (c' : Cocone D') (_ : IsColimit c') (ei : Zi ≅ Spec c'.pt),
      ∀ j, ei.inv ≫ l j ≫ (ez j).hom = Spec.map (c'.ι.app j) := by
  let q : ∀ j, D.obj j ⟶ D'.obj j := fun j => Spec.preimage ((ez j).inv ≫ φ j)
  have hqs : ∀ j, Spec.map (q j) = (ez j).inv ≫ φ j := fun j => Spec.map_preimage _
  let c' : Cocone D' :=
    { pt := Γ(Zi, ⊤)
      ι := { app := fun j => Spec.preimage (Zi.isoSpec.inv ≫ l j ≫ (ez j).hom)
             naturality := fun j j' g => Spec.map_injective (by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Spec.map_comp,
                 Spec.map_preimage, ← hr g, Category.assoc, Iso.hom_inv_id_assoc]
               rw [← Category.assoc (l j'), hl g, ← Category.assoc]) } }
  have hcs : ∀ j, Spec.map (c'.ι.app j) = Zi.isoSpec.inv ≫ l j ≫ (ez j).hom := fun j => Spec.map_preimage _
  let qi : c.pt ⟶ c'.pt := Spec.preimage (Zi.isoSpec.inv ≫ φi)
  have hqis : Spec.map qi = Zi.isoSpec.inv ≫ φi := Spec.map_preimage _
  have hepi : ∀ j, Epi (q j) := fun j => by
    have : IsClosedImmersion (Spec.map (q j)) := by rw [hqs]; infer_instance
    exact epi_of_closed _
  have hq : ∀ {j j' : J} (g : j ⟶ j'), D.map g ≫ q j' = q j ≫ D'.map g := fun {j j'} g =>
    Spec.map_injective (by
      simp only [Spec.map_comp, hqs, ← hr g, Category.assoc, Iso.hom_inv_id_assoc, hφ g])
  have hqi : ∀ j, c.ι.app j ≫ qi = q j ≫ c'.ι.app j := fun j => Spec.map_injective (by
    simp only [Spec.map_comp, hqs, hcs, hqis, Category.assoc, Iso.hom_inv_id_assoc, hlφ])
  obtain ⟨j0⟩ := ‹Nonempty J›
  have hp : IsPushout (c.ι.app j0) (q j0) qi (c'.ι.app j0) := by
    apply isPushout_of_Spec
    refine IsPullback.of_iso (hpb j0).flip Zi.isoSpec (Iso.refl _) (ez j0) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hqis]
    · simp [hcs]
    · simp
    · simp [hqs]
  exact ⟨c', colimOfPushout hc c' q hq hepi qi hqi j0 hp, Zi.isoSpec, fun j => (hcs j).symm⟩

end UpperTheory.PushoutColimitSpec

open UpperTheory.PushoutColimitSpec in
theorem UpperTheory.exists_closedFiber_colimit_presentation :
    ∀ {B W : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (x : U.left) (S : SHSys U x)
        (zl : ∀ j, pullback (S.t ≫ U.hom) ι ⟶ pullback (S.V j).hom ι),
        (∀ j, zl j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (S.c.ι.app j) ≫ (S.e j).inv) →
        (∀ j, zl j ≫ pullback.snd _ _ = pullback.snd _ _) →
        ∃ (D' : S.J ⥤ CommRingCat.{0}) (c' : Cocone D') (_ : IsColimit c')
          (ez : ∀ j, pullback (S.V j).hom ι ≅ Spec (D'.obj j)) (ei : pullback (S.t ≫ U.hom) ι ≅ Spec c'.pt),
          (∀ {j j' : S.J} (g : j ⟶ j'), (ez j').inv ≫ resBW ι (S.tr g) ≫ (ez j).hom = Spec.map (D'.map g)) ∧
          (∀ j, ei.inv ≫ zl j ≫ (ez j).hom = Spec.map (c'.ι.app j)) := by
  intro B W ι _ U x S zl h1 h2
  have rfst : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (S.tr g).left := fun g => pullback.lift_fst _ _ _
  have rsnd : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ pullback.snd _ _ = pullback.snd _ _ := fun g =>
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have htr : ∀ {j j' : S.J} (g : j ⟶ j'),
      (S.tr g).left = (S.e j').hom ≫ Spec.map (S.D.map g) ≫ (S.e j).inv := fun g => by
    rw [← S.tr_spec g]; simp
  have hid : ∀ j, resBW ι (S.tr (𝟙 j)) = 𝟙 _ := fun j => by
    apply pullback.hom_ext
    · rw [rfst, htr]; simp
    · rw [rsnd]; simp
  have hcomp : ∀ {j j' j'' : S.J} (g : j ⟶ j') (g' : j' ⟶ j''),
      resBW ι (S.tr (g ≫ g')) = resBW ι (S.tr g') ≫ resBW ι (S.tr g) := fun g g' => by
    apply pullback.hom_ext
    · rw [Category.assoc, rfst, rfst, reassoc_of% (rfst g'), htr, htr, htr]; simp
    · rw [Category.assoc, rsnd, rsnd, rsnd]
  have hVa : ∀ j, IsAffine (S.V j).left := fun j => .of_isIso (S.e j).hom
  let φ : ∀ j, pullback (S.V j).hom ι ⟶ Spec (S.D.obj j) := fun j => pullback.fst _ _ ≫ (S.e j).hom
  have hφc : ∀ j, IsClosedImmersion (φ j) := fun j => inferInstance
  have hZa : ∀ j, IsAffine (pullback (S.V j).hom ι) := fun j => by
    have h := (IsClosedImmersion.isAffine_surjective_of_isAffine (φ j)).1
    exact h
  have hZi : IsAffine (pullback (S.t ≫ U.hom) ι) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.fst (S.t ≫ U.hom) ι)).1
  obtain ⟨D', ez, hr⟩ := ring_system (fun j => pullback (S.V j).hom ι) (fun g => resBW ι (S.tr g)) hid hcomp
  have hφ : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ φ j = φ j' ≫ Spec.map (S.D.map g) := fun {j j'} g => by
    simp only [φ]
    rw [reassoc_of% (rfst g), htr]; simp
  have hl : ∀ {j j' : S.J} (g : j ⟶ j'), zl j' ≫ resBW ι (S.tr g) = zl j := fun {j j'} g => by
    apply pullback.hom_ext
    · rw [Category.assoc, rfst, reassoc_of% (h1 j'), h1, htr]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Spec.map_comp_assoc, S.c.w]
    · rw [Category.assoc, rsnd, h2, h2]
  have hlφ : ∀ j, zl j ≫ φ j = pullback.fst _ _ ≫ Spec.map (S.c.ι.app j) := fun j => by
    simp only [φ]
    rw [reassoc_of% (h1 j)]; simp
  have hpb : ∀ j, IsPullback (zl j) (pullback.fst (S.t ≫ U.hom) ι) (φ j) (Spec.map (S.c.ι.app j)) := fun j => by
    have hw : (S.a j).left ≫ U.hom = (S.V j).hom := by simpa using (S.a j).w
    have hb : (Spec.map (S.c.ι.app j) ≫ (S.e j).inv) ≫ (S.V j).hom = S.t ≫ U.hom := by
      rw [S.ht j, ← hw]; simp
    have big : IsPullback (zl j ≫ pullback.snd _ _) (pullback.fst (S.t ≫ U.hom) ι) ι
        ((Spec.map (S.c.ι.app j) ≫ (S.e j).inv) ≫ (S.V j).hom) := by
      rw [h2, hb]; exact (IsPullback.of_hasPullback _ _).flip
    have sq := IsPullback.of_right big (h1 j) (IsPullback.of_hasPullback (S.V j).hom ι).flip
    exact IsPullback.of_iso sq (Iso.refl _) (Iso.refl _) (Iso.refl _) (S.e j) (by simp) (by simp) (by simp [φ]) (by simp)
  have : Nonempty S.J := IsFiltered.nonempty
  obtain ⟨c', hc', ei, he⟩ := cocone_system (fun j => pullback (S.V j).hom ι) (fun g => resBW ι (S.tr g)) S.D D' ez hr
    S.c S.hc φ hφ (pullback (S.t ≫ U.hom) ι) (pullback.fst _ _) zl hl hlφ hpb
  exact ⟨D', c', hc', ez, ei, hr, he⟩
