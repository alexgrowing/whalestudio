import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHom
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Obs.GluePair

open Opposite Limits GlobalTheory.LiftSys.Glue

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {X₀ Z₀ : Scheme.{0}} {t₀ : Z₀ ⟶ Sp R₀}

abbrev fh {f₀ : Z₀ ⟶ X₀} {T₁ T₂ : Pair f₀} (a : T₁ ⟶ T₂) : (op T₂.1.1 : AffOp Z₀) ⟶ op T₁.1.1 :=
  (homOfLE (Pair.le_fst (leOfHom a))).op

abbrev cov {S' : Sys I π t₀} {Z : Scheme.{0}} {t : Z ⟶ Sp R} {k : Z₀ ⟶ Z} (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀)
    (hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z) : Z.OpenCover where
  I₀ := Pair f₀
  X T := Sp (S'.F.obj (op T.1.1))
  f T := P'.y (op T.1.1)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x ↦ by obtain ⟨T, z, hz⟩ := hc x; exact ⟨T, z, hz⟩, fun T ↦ P'.isOpen _⟩

def dir {S' : Sys I π t₀} {Z : Scheme.{0}} {t : Z ⟶ Sp R} {k : Z₀ ⟶ Z} (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀)
    (hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z)
    (hd : ∀ (T₁ T₂ : Pair f₀) (a : Sp (S'.F.obj (op T₁.1.1))) (b : Sp (S'.F.obj (op T₂.1.1))),
      P'.y (op T₁.1.1) a = P'.y (op T₂.1.1) b → ∃ (T₃ : Pair f₀) (_ : T₃ ≤ T₁) (_ : T₃ ≤ T₂)
        (c : Sp (S'.F.obj (op T₃.1.1))), P'.y (op T₃.1.1) c = P'.y (op T₁.1.1) a) :
    (cov P' f₀ hc).LocallyDirected where
  trans {T₁ T₂} a := spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1))
  trans_id T := by
    haveI := P'.isOpen (op T.1.1)
    rw [← cancel_mono (P'.y (op T.1.1))]
    exact (P'.nat _).trans (Category.id_comp _).symm
  trans_comp {T₁ T₂ T₃} a b := by
    haveI := P'.isOpen (op T₃.1.1)
    rw [← cancel_mono (P'.y (op T₃.1.1))]
    rw [Category.assoc]
    exact (P'.nat _).trans ((congrArg (_ ≫ ·) (P'.nat _)).trans (P'.nat _)).symm
  w {T₁ T₂} a := P'.nat _
  directed {T₁ T₂} x := by
    haveI := P'.isOpen (op T₁.1.1)
    haveI := P'.isOpen (op T₂.1.1)
    obtain ⟨T₃, h₁, h₂, c, hcT⟩ := hd T₁ T₂ (pullback.fst (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) x)
      (pullback.snd (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) x)
      (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])
    refine ⟨T₃, homOfLE h₁, homOfLE h₂, c, ?_⟩
    apply (pullback.fst (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) ≫ P'.y (op T₁.1.1)).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change (spMap _ ≫ P'.y (op T₁.1.1)) c = _
    rw [P'.nat, hcT, Scheme.Hom.comp_apply]
  property_trans {T₁ T₂} a := by
    haveI := P'.isOpen (op T₂.1.1)
    haveI : IsOpenImmersion (spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)) ≫
        P'.y (op T₂.1.1)) := by
      rw [P'.nat]; exact P'.isOpen _
    exact IsOpenImmersion.of_comp _ (P'.y (op T₂.1.1))

end GlobalTheory.Obs.GluePair

namespace GlobalTheory.Obs

open Opposite Limits GlobalTheory.LiftSys.Glue GlobalTheory.Obs.GluePair

theorem pairs_glue : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l → ∃ f : Z ⟶ X, f ≫ s = t ∧ k ≫ f = f₀ ≫ i := by
  intro R R₀ _ _ I hI π hπ hk X₀ Z₀ X Z s₀ t₀ s t i k hi hkk S S' P P' f₀ h l hL hN
  have hsurU : ∀ W, Function.Surjective (spMap (S'.p W)) := fun W ↦
    spMap_surjective _ (S'.surj W) fun b hb ↦ by
      have hb' := (S'.ker W b).1 hb
      have : b * b ∈ (I.map (algebraMap R (S'.F.obj W))) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
      rwa [map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hπs : Function.Surjective (spMap π) := spMap_surjective π hπ fun a ha ↦ by
    have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
    have : a * a ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha' ha'
    rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI hkc : IsClosedImmersion k := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hkk.flip inferInstance
  have hinj : Function.Injective k := k.isClosedEmbedding.injective
  have hksurj : Function.Surjective k :=
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hkk.flip ⟨hπs⟩).surj

  have hrng : ∀ (W : Z₀.affineOpens) (w : Sp (S'.F.obj (op W))), ∃ z₀ ∈ W.1, P'.y (op W) w = k z₀ := by
    intro W w
    obtain ⟨v, rfl⟩ := hsurU (op W) w
    refine ⟨affPt t₀ W v, W.2.range_fromSpec.le ⟨v, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, P'.red (op W), Scheme.Hom.comp_apply]
  have hcov : ∀ (W : Z₀.affineOpens) (z₀ : Z₀), z₀ ∈ W.1 → ∃ w : Sp (S'.F.obj (op W)), P'.y (op W) w = k z₀ := by
    intro W z₀ hz
    obtain ⟨v, hv⟩ : z₀ ∈ Set.range (affPt t₀ W) := W.2.range_fromSpec.ge hz
    refine ⟨spMap (S'.p (op W)) v, ?_⟩
    change (spMap (S'.p (op W)) ≫ P'.y (op W)) v = k z₀
    rw [P'.red (op W), Scheme.Hom.comp_apply]
    exact congrArg k hv

  have hpair : ∀ (z₀ : Z₀) (U : X₀.affineOpens), f₀ z₀ ∈ U.1 → ∀ V : Z₀.Opens, z₀ ∈ V →
      ∃ T : Pair f₀, z₀ ∈ T.1.1.1 ∧ T.1.2 = U ∧ T.1.1.1 ≤ V := by
    intro z₀ U hU V hV
    obtain ⟨W, hW, hWle⟩ := exists_affine (show z₀ ∈ V ⊓ f₀ ⁻¹ᵁ U.1 from ⟨hV, hU⟩)
    exact ⟨⟨(W, U), hWle.trans inf_le_right⟩, hW, rfl, hWle.trans inf_le_left⟩
  have hpt : ∀ z₀ : Z₀, ∃ T : Pair f₀, z₀ ∈ T.1.1.1 := by
    intro z₀
    obtain ⟨U, hU, -⟩ := exists_affine (show f₀ z₀ ∈ (⊤ : X₀.Opens) from trivial)
    obtain ⟨T, hT, -, -⟩ := hpair z₀ U hU ⊤ trivial
    exact ⟨T, hT⟩
  have hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z := by
    intro z
    obtain ⟨z₀, rfl⟩ := hksurj z
    obtain ⟨T, hT⟩ := hpt z₀
    obtain ⟨w, hw⟩ := hcov T.1.1 z₀ hT
    exact ⟨T, w, hw⟩
  have hd : ∀ (T₁ T₂ : Pair f₀) (a : Sp (S'.F.obj (op T₁.1.1))) (b : Sp (S'.F.obj (op T₂.1.1))),
      P'.y (op T₁.1.1) a = P'.y (op T₂.1.1) b → ∃ (T₃ : Pair f₀) (_ : T₃ ≤ T₁) (_ : T₃ ≤ T₂)
        (c : Sp (S'.F.obj (op T₃.1.1))), P'.y (op T₃.1.1) c = P'.y (op T₁.1.1) a := by
    intro T₁ T₂ a b hab
    obtain ⟨z₀, h₁, ha⟩ := hrng T₁.1.1 a
    obtain ⟨z₁, h₂, hb⟩ := hrng T₂.1.1 b
    have e : z₀ = z₁ := hinj (ha.symm.trans (hab.trans hb))
    subst e
    have hU₁ : f₀ z₀ ∈ T₁.1.2.1 := T₁.2 h₁
    have hU₂ : f₀ z₀ ∈ T₂.1.2.1 := T₂.2 h₂
    obtain ⟨U₃, hU₃, hU₃le⟩ := exists_affine (show f₀ z₀ ∈ T₁.1.2.1 ⊓ T₂.1.2.1 from ⟨hU₁, hU₂⟩)
    obtain ⟨T₃, hT₃, e₃, hT₃le⟩ := hpair z₀ U₃ hU₃ (T₁.1.1.1 ⊓ T₂.1.1.1) ⟨h₁, h₂⟩
    subst e₃
    obtain ⟨c, hc'⟩ := hcov T₃.1.1 z₀ hT₃
    refine ⟨T₃, ?_, ?_, c, hc'.trans ha.symm⟩
    · exact Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(le_inf_iff.1 hT₃le).1, (le_inf_iff.1 hU₃le).1⟩)
    · exact Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(le_inf_iff.1 hT₃le).2, (le_inf_iff.1 hU₃le).2⟩)
  letI := dir P' f₀ hc hd
  let 𝒰 := cov P' f₀ hc
  let lr : ∀ T : Pair f₀, S.F.obj (op T.1.2) →+* S'.F.obj (op T.1.1) := fun T ↦ (l (op T)).toRingHom
  let g : ∀ T : 𝒰.I₀, 𝒰.X T ⟶ X := fun T ↦ spMap (lr T) ≫ P.y (op T.1.2)
  have hg : ∀ {T₁ T₂ : 𝒰.I₀} (a : T₁ ⟶ T₂), 𝒰.trans a ≫ g T₂ = g T₁ := by
    intro T₁ T₂ a
    change spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)) ≫
      spMap (lr T₂) ≫ P.y (op T₂.1.2) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)).comp (lr T₂) =
        (lr T₁).comp (mp S.F (homOfLE (Pair.le_snd (leOfHom a))).op : S.F.obj (op T₂.1.2) →+* S.F.obj (op T₁.1.2)) :=
      RingHom.ext fun b ↦ hN a.op b
    rw [e, spMap_comp₂, Category.assoc, P.nat]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g hg, 𝒰.hom_ext _ _ fun T ↦ ?_, ?_⟩
  · rw [𝒰.map_glueMorphismsOfLocallyDirected_assoc g hg T]
    change (spMap (lr T) ≫ P.y (op T.1.2)) ≫ s = P'.y (op T.1.1) ≫ t
    rw [Category.assoc, P.base, P'.base, ← spMap_comp₂]
    exact congrArg spMap (RingHom.ext fun r ↦ (l (op T)).commutes r)
  · let 𝒱 : Z₀.OpenCover := Scheme.Cover.mkOfCovers (Pair f₀) (fun T ↦ Sp (GlobalTheory.CechDR.Sec t₀ T.1.1.1))
      (fun T ↦ affPt t₀ T.1.1)
      (fun z ↦ by
        obtain ⟨T, hT⟩ := hpt z
        obtain ⟨w, hw⟩ : z ∈ Set.range (affPt t₀ T.1.1) := T.1.1.2.range_fromSpec.ge hT
        exact ⟨T, w, hw⟩)
      (fun T ↦ IsAffineOpen.isOpenImmersion_fromSpec T.1.1.2)
    refine 𝒱.hom_ext _ _ fun T ↦ ?_
    change affPt t₀ T.1.1 ≫ k ≫ _ = affPt t₀ T.1.1 ≫ f₀ ≫ i
    rw [← Category.assoc, show affPt t₀ T.1.1 ≫ k = _ from (P'.red (op T.1.1)).symm, Category.assoc]
    change spMap (S'.p (op T.1.1)) ≫ 𝒰.f T ≫ _ = _
    rw [𝒰.map_glueMorphismsOfLocallyDirected g hg T]
    change spMap (S'.p (op T.1.1)) ≫ spMap (lr T) ≫ P.y (op T.1.2) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (S'.p (op T.1.1)).comp (lr T) = (GlobalTheory.CechDR.secPull s₀ t₀ T).comp (S.p (op T.1.2)) :=
      RingHom.ext fun b ↦ hL (op T) b
    rw [e, spMap_comp₂, Category.assoc, show spMap (S.p (op T.1.2)) ≫ P.y (op T.1.2) = affPt s₀ T.1.2 ≫ i from P.red _,
      ← Category.assoc, GlobalTheory.CechDR.secPull_affPt (φ := f₀) s₀ t₀ T, Category.assoc]

end GlobalTheory.Obs
