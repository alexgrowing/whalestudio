import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjRestrictSnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.Zar

variable {S : Scheme.{0}} {A : Over S}

theorem same_comp {T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) (z : Z ⟶ Y) : Same A N M (z ≫ y) (z ≫ u) := by
  rw [same_iff hN hM] at h ⊢
  have e := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) h
  simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using e

theorem same_ev_iff {T U V Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (j : V ⟶ T) (y : Y ⟶ V) (u : Y ⟶ U) :
    Same A (ev N (fst A V) (snd A V ≫ j)) M y u ↔ Same A N M (y ≫ j) u := by
  rw [same_iff (pull_isLB hN _) hM, same_iff hN hM, evc_ev hN]
  simp only [lift_fst, lift_snd_assoc, Category.assoc]

theorem exists_restrict {T Y Z : Over S} (y : Y ⟶ T) (z : Z ⟶ T) [IsOpenImmersion z.left] (p : Y.left)
    (hp : y.left p ∈ Set.range z.left) :
    ∃ (Y' : Over S) (i : Y' ⟶ Y) (t : Y' ⟶ Z), IsOpenImmersion i.left ∧ p ∈ Set.range i.left ∧ t ≫ z = i ≫ y := by
  let V := y.left ⁻¹ᵁ z.left.opensRange
  let Y' : Over S := Over.mk (V.ι ≫ Y.hom)
  let i : Y' ⟶ Y := Over.homMk V.ι rfl
  have hr : Set.range (i ≫ y).left ⊆ Set.range z.left := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  let t : Y' ⟶ Z := Over.homMk (IsOpenImmersion.lift z.left (i ≫ y).left hr) (by
    rw [← Over.w z, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  refine ⟨Y', i, t, inferInstanceAs (IsOpenImmersion V.ι), ⟨⟨p, hp⟩, rfl⟩, ?_⟩
  ext1; exact IsOpenImmersion.lift_fac _ _ _

variable [GrpObj A]

theorem exists_same_of_local (hA : IsAbelianScheme A) {T U Y : Over S} {N : LB (A ⊗ T).left}
    {M : LB (A ⊗ U).left} (hN : Fam A N) (hM : Fam A M) (hI : Inj A M) (y : Y ⟶ T)
    (loc : ∀ p : Y.left, ∃ (Z : Over S) (z : Z ⟶ Y) (u : Z ⟶ U), IsOpenImmersion z.left ∧
      p ∈ Set.range z.left ∧ Same A N M (z ≫ y) u) : ∃ u : Y ⟶ U, Same A N M y u := by
  choose Z z u ho hp hs using loc
  let 𝒰 : Y.left.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Y.left (fun p ↦ (Z p).left)
    (fun p ↦ (z p).left) (fun p ↦ by obtain ⟨q, hq⟩ := hp p; exact ⟨p, q, hq⟩) ho
  have hc : ∀ p q : Y.left, pullback.fst (z p).left (z q).left ≫ (u p).left =
      pullback.snd (z p).left (z q).left ≫ (u q).left := by
    intro p q
    let P : Over S := Over.mk (pullback.fst (z p).left (z q).left ≫ (Z p).hom)
    let a : P ⟶ Z p := Over.homMk (pullback.fst (z p).left (z q).left) rfl
    let b : P ⟶ Z q := Over.homMk (pullback.snd (z p).left (z q).left) (by
      rw [← Over.w (z q), ← Category.assoc, ← pullback.condition, Category.assoc, Over.w]; rfl)
    have hab : a ≫ z p = b ≫ z q := by ext1; exact pullback.condition
    have h₁ := same_comp hN.isLB hM.isLB (hs p) a
    have h₂ := same_comp hN.isLB hM.isLB (hs q) b
    rw [← Category.assoc, hab, Category.assoc] at h₁
    rw [same_iff hN.isLB hM.isLB] at h₁ h₂
    have h := hI P _ _ ((same_iff hM.isLB hM.isLB _ _).2 (h₁.symm.trans h₂))
    exact congrArg (·.left) h
  have hg : ∀ p, (z p).left ≫ 𝒰.glueMorphisms (fun p ↦ (u p).left) hc = (u p).left :=
    𝒰.ι_glueMorphisms _ hc
  let g : Y ⟶ U := Over.homMk (𝒰.glueMorphisms (fun p ↦ (u p).left) hc) (𝒰.hom_ext _ _ fun (p : Y.left) ↦
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) (hg p))).trans
      ((Over.w (u p)).trans (Over.w (z p)).symm))
  refine ⟨g, same_of_local S A T U hA N M hN hM Y y g fun p ↦ ⟨Z p, z p, ho p, hp p, ?_⟩⟩
  have e : z p ≫ g = u p := by ext1; exact hg p
  rw [e]
  exact hs p

theorem fam_ev {T Y : Over S} {N : LB (A ⊗ T).left} (h : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hM : (AbDual.ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add _ _ _ _

end GlobalTheory.DualCon.Zar

namespace GlobalTheory.DualCon

theorem chartAt_of_affine : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M →
    (∀ (T : Over S) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) →
    ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro S A _ hA U M hM hI aff T N hN
  let W : Set T.left := {x | ∃ (Z : Over S) (z : Z ⟶ T) (u : Z ⟶ U), IsOpenImmersion z.left ∧
    x ∈ Set.range z.left ∧ Same A N M z u}
  have hW : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨Z, z, u, ho, hx, hs⟩
    exact ⟨Set.range z.left, fun x' hx' ↦ ⟨Z, z, u, ho, hx', hs⟩, z.left.opensRange.2, hx⟩
  refine ⟨⟨W, hW⟩, fun Y y ↦ ⟨?_, fun h ↦ ?_⟩⟩
  · rintro ⟨u, hu⟩ p
    obtain ⟨i, q, hq⟩ := T.left.affineCover.exists_eq (y.left p)
    let V : Over S := Over.mk (T.left.affineCover.f i ≫ T.hom)
    let j : V ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
    haveI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (T.left.affineCover.f i))
    haveI : IsAffine V.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
    obtain ⟨O, hO⟩ := aff V _ (Zar.fam_ev hN j)
    obtain ⟨Y', c, t, -, ⟨r, hr⟩, ht⟩ := Zar.exists_restrict y j p ⟨q, hq⟩
    have h₁ : t.left r ∈ O := (hO Y' t).1 ⟨c ≫ u, by
      rw [Zar.same_ev_iff hN.isLB hM.isLB, ht]
      exact Zar.same_comp hN.isLB hM.isLB hu c⟩ r
    let Z : Over S := Over.mk (O.ι ≫ V.hom)
    let k : Z ⟶ V := Over.homMk O.ι rfl
    haveI : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion O.ι)
    obtain ⟨v, hv⟩ := (hO Z k).2 fun w ↦ w.2
    refine ⟨Z, k ≫ j, v, by rw [Over.comp_left]; infer_instance, ⟨⟨t.left r, h₁⟩, ?_⟩,
      (Zar.same_ev_iff hN.isLB hM.isLB _ _ _).1 hv⟩
    change (t ≫ j).left r = _
    rw [ht, ← hr]
    rfl
  · refine Zar.exists_same_of_local hA hN hM hI y fun p ↦ ?_
    obtain ⟨Z, z, u, ho, hx, hs⟩ := h p
    obtain ⟨Y', c, t, hc, hp, ht⟩ := Zar.exists_restrict y z p hx
    exact ⟨Y', c, t ≫ u, hc, hp, ht ▸ Zar.same_comp hN.isLB hM.isLB hs t⟩

end GlobalTheory.DualCon
