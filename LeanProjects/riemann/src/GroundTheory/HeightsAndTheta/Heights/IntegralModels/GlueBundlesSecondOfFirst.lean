import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section Abstract

variable {X : Scheme.{0}} {ι : Type} (U : X.Opens) (Xp : ι → Scheme.{0}) (q : ∀ p, Xp p ⟶ X)

def GlueFrame {G : Scheme.{0}} (t : G ⟶ U) (r : ∀ p, G ⟶ Xp p)
    (h : ∀ p, t ≫ U.ι = r p ≫ q p) : Prop :=
  ∀ (E₀ : (U : Scheme.{0}).Modules) (Ep : ∀ p, (Xp p).Modules), IsVectorBundle E₀ →
    (∀ p, IsVectorBundle (Ep p)) →
    ∀ γ : ∀ p, (Scheme.Modules.pullback (r p)).obj (Ep p) ≅ (Scheme.Modules.pullback t).obj E₀,
    ∃ E : X.Modules, IsVectorBundle E ∧
      ∃ (α : (Scheme.Modules.pullback U.ι).obj E ≅ E₀)
        (β : ∀ p, (Scheme.Modules.pullback (q p)).obj E ≅ Ep p),
        ∀ p, (pbSquare t U.ι (r p) (q p) (h p) E).hom ≫
            (Scheme.Modules.pullback (r p)).map (β p).hom ≫ (γ p).hom =
          (Scheme.Modules.pullback t).map α.hom

end Abstract

section PullbackFacts

variable {A B C D : Scheme.{0}}

theorem faithful_pullback_of_isIso (ψ : A ⟶ B) [IsIso ψ] :
    (Scheme.Modules.pullback ψ).Faithful :=
  Functor.Faithful.of_comp_iso (G := Scheme.Modules.pullback (inv ψ))
    ((Scheme.Modules.pullbackComp (inv ψ) ψ) ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id ψ) ≪≫ Scheme.Modules.pullbackId B)

@[reassoc]
theorem pullbackComp_inv_congr {G : Scheme.{0}} (ψ : G ⟶ A) {a b : A ⟶ D} (e : a = b)
    (M : D.Modules) (E' : (Scheme.Modules.pullback (ψ ≫ a)).obj M =
      (Scheme.Modules.pullback (ψ ≫ b)).obj M) :
    eqToHom E' ≫ (Scheme.Modules.pullbackComp ψ b).inv.app M =
      (Scheme.Modules.pullbackComp ψ a).inv.app M ≫
        (Scheme.Modules.pullback ψ).map ((Scheme.Modules.pullbackCongr e).hom.app M) := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

theorem pbSquare_comp {G : Scheme.{0}} (ψ : G ⟶ A) (t : A ⟶ B) (j : B ⟶ D) (k : A ⟶ C)
    (r : C ⟶ D) (h : t ≫ j = k ≫ r) (h' : (ψ ≫ t) ≫ j = (ψ ≫ k) ≫ r) (M : D.Modules) :
    (pbSquare (ψ ≫ t) j (ψ ≫ k) r h' M).hom =
      ((Scheme.Modules.pullbackComp ψ t).app _).inv ≫
        (Scheme.Modules.pullback ψ).map (pbSquare t j k r h M).hom ≫
          ((Scheme.Modules.pullbackComp ψ k).app _).hom := by
  have a1 := congr_arg (fun τ => τ.app M)
    (Scheme.Modules.pseudofunctor_associativity ψ t j)
  have a2 := congr_arg (fun τ => τ.app M)
    (Scheme.Modules.pseudofunctor_associativity ψ k r)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at a1 a2
  have c2 : (Scheme.Modules.pullbackComp (ψ ≫ k) r).inv.app M =
      eqToHom (by simp) ≫ (Scheme.Modules.pullbackComp ψ (k ≫ r)).inv.app M ≫
        (Scheme.Modules.pullback ψ).map ((Scheme.Modules.pullbackComp k r).inv.app M) ≫
          (Scheme.Modules.pullbackComp ψ k).hom.app ((Scheme.Modules.pullback r).obj M) := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp (ψ ≫ k) r).hom.app M)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [a2]
    simp
  simp only [pbSquare, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [c2]
  rw [← cancel_epi ((Scheme.Modules.pullbackComp ψ (t ≫ j)).inv.app M ≫
    (Scheme.Modules.pullback ψ).map ((Scheme.Modules.pullbackComp t j).inv.app M) ≫
      (Scheme.Modules.pullbackComp ψ t).hom.app ((Scheme.Modules.pullback j).obj M))]
  simp only [Category.assoc]
  rw [reassoc_of% a1]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]
  rw [pullbackComp_inv_congr_assoc ψ h]
  simp [Scheme.Modules.pullbackCongr]

end PullbackFacts

section Transport

variable {X : Scheme.{0}} {ι : Type} (U : X.Opens) (Xp : ι → Scheme.{0}) (q : ∀ p, Xp p ⟶ X)

theorem pullback_comp_map {G A D : Scheme.{0}} (ψ : G ⟶ A) (r : A ⟶ D) {M N : D.Modules}
    (x : M ⟶ N) : (Scheme.Modules.pullback (ψ ≫ r)).map x =
      (Scheme.Modules.pullbackComp ψ r).inv.app M ≫
        (Scheme.Modules.pullback ψ).map ((Scheme.Modules.pullback r).map x) ≫
          (Scheme.Modules.pullbackComp ψ r).hom.app N := by
  rw [← Functor.comp_map (Scheme.Modules.pullback r) (Scheme.Modules.pullback ψ),
    (Scheme.Modules.pullbackComp ψ r).hom.naturality x]
  simp

theorem GlueFrame.of_comp {G₁ G₂ : Scheme.{0}} (ψ : G₁ ⟶ G₂)
    [(Scheme.Modules.pullback ψ).Faithful] (t : G₂ ⟶ U) (r : ∀ p, G₂ ⟶ Xp p)
    (h : ∀ p, t ≫ U.ι = r p ≫ q p) (h₁ : ∀ p, (ψ ≫ t) ≫ U.ι = (ψ ≫ r p) ≫ q p)
    (H : GlueFrame U Xp q (ψ ≫ t) (fun p => ψ ≫ r p) h₁) : GlueFrame U Xp q t r h := by
  intro E₀ Ep h0 hp γ
  obtain ⟨E, hE, α, β, hc⟩ := H E₀ Ep h0 hp (fun p =>
    ((Scheme.Modules.pullbackComp ψ (r p)).app (Ep p)).symm ≪≫
      (Scheme.Modules.pullback ψ).mapIso (γ p) ≪≫ (Scheme.Modules.pullbackComp ψ t).app E₀)
  refine ⟨E, hE, α, β, fun p => (Scheme.Modules.pullback ψ).map_injective ?_⟩
  have hp' := hc p
  rw [pbSquare_comp ψ t U.ι (r p) (q p) (h p), pullback_comp_map, pullback_comp_map] at hp'
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_app_assoc] at hp'
  rw [← cancel_epi ((Scheme.Modules.pullbackComp ψ t).inv.app _),
    ← cancel_mono ((Scheme.Modules.pullbackComp ψ t).hom.app _)]
  simpa only [Functor.map_comp, Category.assoc] using hp'

end Transport

section Congr

variable {X : Scheme.{0}} {ι : Type}

theorem GlueFrame.congr (U : X.Opens) (Xp : ι → Scheme.{0}) (q : ∀ p, Xp p ⟶ X) {G : Scheme.{0}}
    {t t' : G ⟶ U} {r r' : ∀ p, G ⟶ Xp p} (ht : t = t') (hr : r = r')
    (h : ∀ p, t ≫ U.ι = r p ≫ q p) (h' : ∀ p, t' ≫ U.ι = r' p ≫ q p) :
    GlueFrame U Xp q t r h ↔ GlueFrame U Xp q t' r' h' := by
  subst ht hr
  rfl

theorem GlueFrame.congr_open (Xp : ι → Scheme.{0}) (q : ∀ p, Xp p ⟶ X) {U U' : X.Opens}
    (hU : U = U') {G : Scheme.{0}} (t : G ⟶ U) (t' : G ⟶ U') (ht : t ≫ U.ι = t' ≫ U'.ι)
    (r : ∀ p, G ⟶ Xp p) (h : ∀ p, t ≫ U.ι = r p ≫ q p) (h' : ∀ p, t' ≫ U'.ι = r p ≫ q p) :
    GlueFrame U Xp q t r h ↔ GlueFrame U' Xp q t' r h' := by
  subst hU
  obtain rfl : t = t' := (cancel_mono U.ι).1 ht
  rfl

theorem GlueFrame.congr_rings (U : X.Opens) (f : X ⟶ Spec (.of ℤ)) (R : ι → CommRingCat.{0})
    {c c' : ∀ p, CommRingCat.of ℤ ⟶ R p} (hc : c = c') {G : Scheme.{0}} (t : G ⟶ U)
    (r : ∀ p, G ⟶ pullback f (Spec.map (c p))) (r' : ∀ p, G ⟶ pullback f (Spec.map (c' p)))
    (hr₁ : ∀ p, r p ≫ pullback.fst _ _ = r' p ≫ pullback.fst _ _)
    (hr₂ : ∀ p, r p ≫ pullback.snd _ _ = r' p ≫ pullback.snd _ _)
    (h : ∀ p, t ≫ U.ι = r p ≫ pullback.fst _ _) (h' : ∀ p, t ≫ U.ι = r' p ≫ pullback.fst _ _) :
    GlueFrame U (fun p => pullback f (Spec.map (c p))) (fun _ => pullback.fst _ _) t r h ↔
      GlueFrame U (fun p => pullback f (Spec.map (c' p))) (fun _ => pullback.fst _ _) t r' h' := by
  subst hc
  obtain rfl : r = r' := funext fun p => pullback.hom_ext (hr₁ p) (hr₂ p)
  rfl

end Congr

section Compat

theorem GlueBundles.compat_iff {G V Y Z : Scheme.{0}} (t : G ⟶ V) (j : V ⟶ Z) (r : G ⟶ Y) (q : Y ⟶ Z)
    (g : G ⟶ Z) (e : t ≫ j = g) (e' : r ≫ q = g) (h : t ≫ j = r ≫ q) (E : Z.Modules)
    {E₀ : V.Modules} {Ep : Y.Modules} (α : (Scheme.Modules.pullback j).obj E ≅ E₀)
    (β : (Scheme.Modules.pullback q).obj E ≅ Ep)
    (γ : (Scheme.Modules.pullback r).obj Ep ≅ (Scheme.Modules.pullback t).obj E₀) :
    GroundTheory.Heights₂.Heights.Model.pullbackCompIso e α =
        GroundTheory.Heights₂.Heights.Model.pullbackCompIso e' β ≪≫ γ ↔
      (pbSquare t j r q h E).hom ≫ (Scheme.Modules.pullback r).map β.hom ≫ γ.hom =
        (Scheme.Modules.pullback t).map α.hom := by
  subst e
  rw [Iso.ext_iff]
  simp only [GroundTheory.Heights₂.Heights.Model.pullbackCompIso, pbSquare, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom, Functor.mapIso_hom, Scheme.Modules.pullbackCongr, eqToIso.hom,
    eqToIso.inv, eqToHom_app, eqToHom_refl, Category.assoc]
  constructor
  · intro H
    have H' := congrArg ((Scheme.Modules.pullbackComp t j).hom.app E ≫ ·) H
    simpa using H'.symm
  · intro H
    rw [← H]
    simp

end Compat

section Concrete

variable (X : Scheme.{0}) (S : Finset Nat.Primes)

theorem GlueBundles.primeProd_cast : GroundTheory.Heights₂.Heights.Model.primeProd S = ((primeProd S : ℕ) : ℤ) := by
  simp [GroundTheory.Heights₂.Heights.Model.primeProd, primeProd]

theorem GlueBundles.invOpen_eq :
    GroundTheory.Heights₂.Heights.Model.invOpen (toSpecZ X) (GroundTheory.Heights₂.Heights.Model.primeProd S) =
      invOpen X (primeProd S) := by
  rw [GroundTheory.Heights₂.Heights.Model.invOpen, invOpen, GlueBundles.primeProd_cast]

theorem GlueBundles.genOpen_eq_top : genOpen X (primeProd S) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hsub := GroundTheory.Heights₂.Heights.Model.range_baseChangeMap_subset (toSpecZ X) ℚ
    (GroundTheory.Heights₂.Heights.Model.primeProd S)
    (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _
      (GroundTheory.Heights₂.Heights.Model.primeProd_ne_zero S)) ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, GlueBundles.invOpen_eq] at hsub
  exact hsub

instance GlueBundles.isIso_genOpen_ι : IsIso (genOpen X (primeProd S)).ι := by
  rw [GlueBundles.genOpen_eq_top, ← Scheme.topIso_hom]
  infer_instance

def GlueBundles.genToInv : genFib X ⟶ invOpen X (primeProd S) :=
  inv (genOpen X (primeProd S)).ι ≫ genRes X (primeProd S)

theorem GlueBundles.genToInv_ι : GlueBundles.genToInv X S ≫ (invOpen X (primeProd S)).ι = genTo X := by
  have h := morphismRestrict_ι (genTo X) (invOpen X (primeProd S))
  rw [GlueBundles.genToInv, Category.assoc]
  exact (congrArg (inv (genOpen X (primeProd S)).ι ≫ ·) h).trans (IsIso.inv_hom_id_assoc _ _)

theorem GlueBundles.frame_iff :
    GlueFrame (GroundTheory.Heights₂.Heights.Model.invOpen (toSpecZ X)
        (GroundTheory.Heights₂.Heights.Model.primeProd S))
      (fun p : S => GroundTheory.Heights₂.Heights.Model.baseChange (toSpecZ X) (ZLoc p))
      (fun p => GroundTheory.Heights₂.Heights.Model.baseChangeMap (toSpecZ X) (ZLoc p))
      (GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ
        (GroundTheory.Heights₂.Heights.Model.primeProd S)
        (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _
          (GroundTheory.Heights₂.Heights.Model.primeProd_ne_zero S)))
      (fun p => GroundTheory.Heights₂.Heights.Model.ratToLoc (toSpecZ X) p)
      (fun p => (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι _ _ _ _).trans
        (GroundTheory.Heights₂.Heights.Model.ratToLoc_baseChangeMap _ p).symm) ↔
    GlueFrame (invOpen X (primeProd S)) (fun p : S => atP X p) (fun p => atPTo X p)
      (genRes X (primeProd S)) (fun p => (genOpen X (primeProd S)).ι ≫ genToAtP X p)
      (fun p => glue_square X (primeProd S) p) := by
  have hsq : ∀ p : S, GlueBundles.genToInv X S ≫ (invOpen X (primeProd S)).ι = genToAtP X p ≫ atPTo X p :=
    fun p => (GlueBundles.genToInv_ι X S).trans (genToAtP_atPTo X p).symm
  have hM : ∀ p : S, GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ
      (GroundTheory.Heights₂.Heights.Model.primeProd S)
      (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _
        (GroundTheory.Heights₂.Heights.Model.primeProd_ne_zero S)) ≫
        (GroundTheory.Heights₂.Heights.Model.invOpen (toSpecZ X)
          (GroundTheory.Heights₂.Heights.Model.primeProd S)).ι = genToAtP X p ≫ atPTo X p := fun p =>
    (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι _ _ _ _).trans (genToAtP_atPTo X p).symm
  have step1 := GlueFrame.congr_rings
    (GroundTheory.Heights₂.Heights.Model.invOpen (toSpecZ X) (GroundTheory.Heights₂.Heights.Model.primeProd S))
    (toSpecZ X) (fun p : S => CommRingCat.of (ZLoc p))
    (c := fun p => CommRingCat.ofHom (Int.castRingHom (ZLoc p)))
    (c' := fun p => CommRingCat.ofHom (algebraMap ℤ (ZLoc p)))
    (funext fun p => congrArg CommRingCat.ofHom (RingHom.ext_int _ _))
    (GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ
      (GroundTheory.Heights₂.Heights.Model.primeProd S)
      (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _
        (GroundTheory.Heights₂.Heights.Model.primeProd_ne_zero S)))
    (fun p => GroundTheory.Heights₂.Heights.Model.ratToLoc (toSpecZ X) p) (fun p => genToAtP X p)
    (fun p => (GroundTheory.Heights₂.Heights.Model.ratToLoc_baseChangeMap _ _).trans
      (genToAtP_atPTo X p).symm)
    (fun p => (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
    (fun p => (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι _ _ _ _).trans
        (GroundTheory.Heights₂.Heights.Model.ratToLoc_baseChangeMap _ _).symm) hM
  have step2 := GlueFrame.congr_open (fun p : S => atP X p) (fun p => atPTo X p) (GlueBundles.invOpen_eq X S)
    (GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X) ℚ
      (GroundTheory.Heights₂.Heights.Model.primeProd S)
      (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_rat _
        (GroundTheory.Heights₂.Heights.Model.primeProd_ne_zero S)))
    (GlueBundles.genToInv X S) ((GroundTheory.Heights₂.Heights.Model.toInvOpen_ι _ _ _ _).trans (GlueBundles.genToInv_ι X S).symm)
    (fun p => genToAtP X p) hM hsq
  refine step1.trans (step2.trans ⟨fun H => ?_, fun H => ?_⟩)
  · have := faithful_pullback_of_isIso (inv (genOpen X (primeProd S)).ι)
    refine GlueFrame.of_comp _ _ _ (inv (genOpen X (primeProd S)).ι) _ _ _
      (fun p => by
        simp only [Category.assoc]
        rw [glue_square X _ p]
        simp only [Category.assoc]) ((GlueFrame.congr _ _ _ rfl ?_ _ _).1 H)
    funext p
    simp
  · have := faithful_pullback_of_isIso (genOpen X (primeProd S)).ι
    refine GlueFrame.of_comp _ _ _ (genOpen X (primeProd S)).ι _ _ hsq
      (fun p => by rw [Category.assoc, hsq p, Category.assoc])
      ((GlueFrame.congr _ _ _ ?_ rfl _ _).1 H)
    simp [GlueBundles.genToInv]

end Concrete

theorem GlueBundles.glueBundles_second_of_first (hA : GroundTheory.Heights₂.Heights.Model.GlueBundles.Statement) :
    GlueBundles.Statement := by
  intro X hX S D
  have := hX.1
  have := hX.2
  refine (GlueBundles.frame_iff X S).1 (fun E₀ Ep h0 hp γ => ?_) D.E₀ D.E D.isVB₀ D.isVB D.γ
  obtain ⟨E, hE, α, β, hc⟩ := hA X (toSpecZ X) S E₀ Ep h0 hp γ
  exact ⟨E, hE, α, β, fun p => (GlueBundles.compat_iff _ _ _ _ _ _ _ _ E α (β p) (γ p)).1 (hc p)⟩

end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
