import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgreeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

section Helpers
variable {S : Scheme.{0}} {A : Over S}

theorem same_of_same_of_same {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB)
    (hM : M.IsLB) {y : Y ⟶ T} {u₁ u₂ : Y ⟶ U} (h₁ : Same A N M y u₁) (h₂ : Same A N M y u₂) :
    Same A M M u₁ u₂ := by
  rw [same_iff hN hM] at h₁ h₂
  rw [same_iff hM hM, ← h₁, h₂]

theorem same_ev_param_iff {T U P Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB)
    (hM : M.IsLB) (g : P ⟶ T) (h : P ⟶ U) (w : Y ⟶ P) :
    Same A (ev N (fst A P) (snd A P ≫ g)) (ev M (fst A P) (snd A P ≫ h)) w w ↔ Same A N M (w ≫ g) (w ≫ h) := by
  rw [same_iff (pull_isLB hN _) (pull_isLB hM _), same_iff hN hM, evc_ev hN, evc_ev hM]
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

variable [GrpObj A]

theorem Fam.ev_param {T P : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (g : P ⟶ T) :
    Fam A (ev N (fst A P) (snd A P ≫ g)) := by
  refine ⟨pull_isLB hN.isLB _, (isAdditive_iff (pull_isLB hN.isLB _)).2 fun Y a a' t ↦ ?_⟩
  rw [evc_ev hN.isLB, evc_ev hN.isLB, evc_ev hN.isLB]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Y a a' (t ≫ g)

end Helpers

theorem chartAt_of_lifting : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), LocallyOfFiniteType U.hom → Fam A M → Inj A M → (∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [Mono f], (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → IsOpenImmersion f) → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (y : Spec (CommRingCat.of B) ⟶ T.left) (u₀ : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ U), Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y) (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ y ≫ T.hom) ⟶ T) u₀ → ∃ u : Over.mk (y ≫ T.hom) ⟶ U, Same A N M (Over.homMk y rfl : Over.mk (y ≫ T.hom) ⟶ T) u) → ChartAt A M N := by
  intro R _ _ A _ hA U M hU hM hInj crit T _ hT N hN hlift
  haveI : LocallyOfFiniteType T.hom := hT
  haveI : LocallyOfFiniteType U.hom := hU
  haveI : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  haveI : LocallyOfFiniteType (T ⊗ U).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst T.hom U.hom ≫ T.hom))
  haveI : IsLocallyNoetherian (T ⊗ U).left := LocallyOfFiniteType.isLocallyNoetherian (T ⊗ U).hom
  obtain ⟨G, i, hi, hG⟩ := GlobalTheory.T.exists_closedSubscheme_additiveFamilies_agree (Sp R) A (T ⊗ U) hA _ _ (hN.ev_param (fst T U)) (hM.ev_param (snd T U))
  have key : ∀ (Y : Over (Sp R)) (w : Y ⟶ T ⊗ U),
      Same A N M (w ≫ fst T U) (w ≫ snd T U) ↔ ∃ z : Y ⟶ G, z ≫ i = w := fun Y w ↦
    (same_ev_param_iff hN.isLB hM.isLB _ _ w).symm.trans (hG Y w)
  obtain ⟨f, hfdef⟩ : ∃ f : G.left ⟶ T.left, f = (i ≫ fst T U).left := ⟨_, rfl⟩
  have hf : f ≫ T.hom = G.hom := by rw [hfdef]; exact Over.w (i ≫ fst T U)
  have hfz : ∀ {Y : Over (Sp R)} (z : Y ⟶ G), (z ≫ i ≫ fst T U).left = z.left ≫ f := fun z ↦ by
    rw [hfdef, Over.comp_left]
  haveI : IsClosedImmersion i.left := hi
  haveI : LocallyOfFiniteType (fst T U).left := inferInstanceAs (LocallyOfFiniteType (pullback.fst T.hom U.hom))
  haveI : LocallyOfFiniteType f := by
    rw [hfdef, Over.comp_left]; infer_instance
  haveI : Mono f := ⟨fun {Z} z₁ z₂ he ↦ by
    let a₁ : Over.mk (z₁ ≫ G.hom) ⟶ G := Over.homMk z₁ rfl
    let a₂ : Over.mk (z₁ ≫ G.hom) ⟶ G := Over.homMk z₂ (by
      simp only [Over.mk_hom]; rw [← hf, reassoc_of% he])
    have e₁ : a₁ ≫ i ≫ fst T U = a₂ ≫ i ≫ fst T U := by
      ext1; rw [hfz, hfz]; exact he
    have h₁ := (key _ (a₁ ≫ i)).2 ⟨a₁, rfl⟩
    have h₂ := (key _ (a₂ ≫ i)).2 ⟨a₂, rfl⟩
    simp only [Category.assoc] at h₁ h₂
    rw [← e₁] at h₂
    have e₂ : a₁ ≫ i ≫ snd T U = a₂ ≫ i ≫ snd T U :=
      hInj _ _ _ (same_of_same_of_same hN.isLB hM.isLB h₁ h₂)
    have e₃ : a₁ ≫ i = a₂ ≫ i := CartesianMonoidalCategory.hom_ext _ _ (by simpa using e₁) (by simpa using e₂)
    have e₄ := congrArg (fun q ↦ q.left) e₃
    simp only [Over.comp_left] at e₄
    exact (cancel_mono i.left).1 e₄⟩
  have hyp : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B),
      I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ →
      ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ G.left) (b : Spec (CommRingCat.of B) ⟶ T.left),
        a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b →
        ∃ l : Spec (CommRingCat.of B) ⟶ G.left, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧
          l ≫ f = b := by
    intro B _ _ _ I hI hmI a b hab
    have ha : a ≫ G.hom = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom := by
      rw [← hf, reassoc_of% hab]
    let a' : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom) ⟶ G := Over.homMk a ha
    have hsame : Same A N M (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b) (by simp) :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b ≫ T.hom) ⟶ T) (a' ≫ i ≫ snd T U) := by
      have h₁ := (key _ (a' ≫ i)).2 ⟨a', rfl⟩
      have e : (a' ≫ i) ≫ fst T U = Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b) (by simp) := by
        ext1; rw [Category.assoc, hfz]; exact hab
      rw [e] at h₁
      simpa only [Category.assoc] using h₁
    obtain ⟨u, hu⟩ := hlift B I hI hmI b (a' ≫ i ≫ snd T U) hsame
    obtain ⟨z, hz⟩ := (key _ (lift (Over.homMk b rfl) u)).1 (by rwa [lift_fst, lift_snd])
    have hzf : z.left ≫ f = b := by
      rw [← hfz, ← Category.assoc, hz, lift_fst]; rfl
    refine ⟨z.left, ?_, hzf⟩
    rw [← cancel_mono f, Category.assoc, hzf, hab]
  haveI : IsOpenImmersion f := crit f hyp
  refine ⟨f.opensRange, fun Y y ↦ ⟨?_, fun hy ↦ ?_⟩⟩
  · rintro ⟨u, hu⟩ p
    obtain ⟨z, hz⟩ := (key Y (lift y u)).1 (by rwa [lift_fst, lift_snd])
    have e : z.left ≫ f = y.left := by rw [← hfz, ← Category.assoc, hz, lift_fst]
    rw [← e]
    exact ⟨z.left p, rfl⟩
  · have hr : Set.range y.left ⊆ Set.range f := by
      rintro _ ⟨p, rfl⟩
      simpa using hy p
    have hl : IsOpenImmersion.lift f y.left hr ≫ f = y.left := IsOpenImmersion.lift_fac f y.left hr
    let z : Y ⟶ G := Over.homMk (IsOpenImmersion.lift f y.left hr) (by rw [← hf, reassoc_of% hl, Over.w y])
    refine ⟨z ≫ i ≫ snd T U, ?_⟩
    have h₁ := (key Y (z ≫ i)).2 ⟨z, rfl⟩
    have e : (z ≫ i) ≫ fst T U = y := by
      ext1; rw [Category.assoc, hfz]; exact hl
    rwa [e, Category.assoc] at h₁

end GlobalTheory.DualCon
