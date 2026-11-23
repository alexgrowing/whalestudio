import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LiftSys.Glue

open Opposite Limits

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_surjective {A B : Type} [CommRing A] [CommRing B] (q : A →+* B)
    (hq : Function.Surjective q) (hn : ∀ a, q a = 0 → a * a = 0) : Function.Surjective (spMap q) := by
  intro p
  have hker : RingHom.ker q ≤ p.asIdeal := by
    intro x hx
    have hx2 := hn x (RingHom.mem_ker.1 hx)
    exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
  haveI := p.isPrime
  haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
  rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
  intro x hx
  exact hker (by simpa [RingHom.mem_ker] using hx)

theorem exists_affine {X₀ : Scheme.{0}} {x : X₀} {U : X₀.Opens} (hx : x ∈ U) :
    ∃ W : X₀.affineOpens, x ∈ W.1 ∧ W.1 ≤ U := by
  obtain ⟨W, hW, hxW, hWU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₀.isBasis_affineOpens) hx
  exact ⟨⟨W, hW⟩, hxW, hWU⟩

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

abbrev cov {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x) :
    X.OpenCover where
  I₀ := X₀.affineOpens
  X U := Sp (S.F.obj (op U))
  f U := h.y (op U)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x ↦ by obtain ⟨U, z, hz⟩ := hc x; exact ⟨U, z, hz⟩, fun U ↦ h.isOpen _⟩

def dir {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x)
    (hd : ∀ (U V : X₀.affineOpens) (a : Sp (S.F.obj (op U))) (b : Sp (S.F.obj (op V))),
      h.y (op U) a = h.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S.F.obj (op W))), h.y (op W) c = h.y (op U) a) :
    (cov h hc).LocallyDirected where
  trans {U V} a := spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U))
  trans_id U := by
    haveI := h.isOpen (op U)
    rw [← cancel_mono (h.y (op U))]
    exact (h.nat _).trans (Category.id_comp _).symm
  trans_comp {U V W} a b := by
    haveI := h.isOpen (op W)
    rw [← cancel_mono (h.y (op W))]
    rw [Category.assoc, h.nat, h.nat, h.nat]
  w {U V} a := h.nat a.op
  directed {U V} x := by
    haveI := h.isOpen (op U)
    haveI := h.isOpen (op V)
    obtain ⟨W, hWU, hWV, c, hcW⟩ := hd U V (pullback.fst (h.y (op U)) (h.y (op V)) x)
      (pullback.snd (h.y (op U)) (h.y (op V)) x)
      (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])
    refine ⟨W, homOfLE hWU, homOfLE hWV, c, ?_⟩
    apply (pullback.fst (h.y (op U)) (h.y (op V)) ≫ h.y (op U)).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change (spMap _ ≫ h.y (op U)) c = _
    rw [h.nat, hcW, Scheme.Hom.comp_apply]
  property_trans {U V} a := by
    haveI := h.isOpen (op V)
    haveI : IsOpenImmersion (spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) ≫ h.y (op V)) := by
      rw [h.nat]; exact h.isOpen _
    exact IsOpenImmersion.of_comp _ (h.y (op V))

theorem presents_hom : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (Y : Scheme.{0}) (t : Y ⟶ Sp R) (j : X₀ ⟶ Y), IsPullback i s₀ s (spMap π) → S.Presents t j → S'.Presents s i → (∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b)) → ∃ f : X ⟶ Y, f ≫ t = s ∧ i ≫ f = j := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' X s i Y t j hpb hY hX hψ
  obtain ⟨ψ, hψp, hψn⟩ := hψ

  have hsurU : ∀ U, Function.Surjective (spMap (S'.p U)) := fun U ↦
    spMap_surjective _ (S'.surj U) fun b hb ↦ by
      have hb' := (S'.ker U b).1 hb
      have : b * b ∈ (I.map (algebraMap R (S'.F.obj U))) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
      rwa [map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hπs : Function.Surjective (spMap π) := spMap_surjective π hπ fun a ha ↦ by
    have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
    have : a * a ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha' ha'
    rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this

  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI hic : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip inferInstance
  have hinj : Function.Injective i := i.isClosedEmbedding.injective
  have hisurj : Function.Surjective i :=
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hpb.flip ⟨hπs⟩).surj

  have hrng : ∀ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), ∃ x₀ ∈ U.1, hX.y (op U) z = i x₀ := by
    intro U z
    obtain ⟨w, rfl⟩ := hsurU (op U) z
    refine ⟨affPt s₀ U w, U.2.range_fromSpec.le ⟨w, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hX.red (op U), Scheme.Hom.comp_apply]
  have hcov : ∀ (U : X₀.affineOpens) (x₀ : X₀), x₀ ∈ U.1 → ∃ z : Sp (S'.F.obj (op U)), hX.y (op U) z = i x₀ := by
    intro U x₀ hx
    obtain ⟨w, hw⟩ : x₀ ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hx
    refine ⟨spMap (S'.p (op U)) w, ?_⟩
    change (spMap (S'.p (op U)) ≫ hX.y (op U)) w = i x₀
    rw [hX.red (op U), Scheme.Hom.comp_apply]
    exact congrArg i hw
  have hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), hX.y (op U) z = x := by
    intro x
    obtain ⟨x₀, rfl⟩ := hisurj x
    obtain ⟨U, hxU, -⟩ := exists_affine (show x₀ ∈ (⊤ : X₀.Opens) from trivial)
    obtain ⟨z, hz⟩ := hcov U x₀ hxU
    exact ⟨U, z, hz⟩
  have hd : ∀ (U V : X₀.affineOpens) (a : Sp (S'.F.obj (op U))) (b : Sp (S'.F.obj (op V))),
      hX.y (op U) a = hX.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S'.F.obj (op W))), hX.y (op W) c = hX.y (op U) a := by
    intro U V a b hab
    obtain ⟨x₀, hxU, ha⟩ := hrng U a
    obtain ⟨x₁, hxV, hb⟩ := hrng V b
    have e : x₀ = x₁ := hinj (ha.symm.trans (hab.trans hb))
    subst e
    obtain ⟨W, hxW, hWle⟩ := exists_affine (show x₀ ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
    obtain ⟨c, hc'⟩ := hcov W x₀ hxW
    exact ⟨W, le_inf_iff.1 hWle |>.1, le_inf_iff.1 hWle |>.2, c, hc'.trans ha.symm⟩
  letI := dir hX hc hd
  let 𝒰 := cov hX hc
  let g : ∀ U : 𝒰.I₀, 𝒰.X U ⟶ Y := fun U ↦
    spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)
  have hg : ∀ {U V : 𝒰.I₀} (a : U ⟶ V), 𝒰.trans a ≫ g V = g U := by
    intro U V a
    change spMap (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)) ≫
      spMap (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) ≫ hY.y (op V) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)).comp
        (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) =
        (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)).comp
          (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) :=
      RingHom.ext fun b ↦ hψn (op V) (op U) a.op b
    rw [e, spMap_comp₂, Category.assoc, hY.nat a.op]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g hg, 𝒰.hom_ext _ _ fun U ↦ ?_, ?_⟩
  · rw [𝒰.map_glueMorphismsOfLocallyDirected_assoc g hg U]
    change (spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)) ≫ t = hX.y (op U) ≫ s
    rw [Category.assoc, hY.base, hX.base, ← spMap_comp₂]
    exact congrArg spMap (RingHom.ext fun r ↦ (ψ (op U)).commutes r)
  · let 𝒱 : X₀.OpenCover := Scheme.Cover.mkOfCovers X₀.affineOpens (fun U ↦ Sp (Sec s₀ U.1))
      (fun U ↦ affPt s₀ U)
      (fun x ↦ by
        obtain ⟨U, hxU, -⟩ := exists_affine (show x ∈ (⊤ : X₀.Opens) from trivial)
        obtain ⟨w, hw⟩ : x ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hxU
        exact ⟨U, w, hw⟩)
      (fun U ↦ IsAffineOpen.isOpenImmersion_fromSpec U.2)
    refine 𝒱.hom_ext _ _ fun U ↦ ?_
    change affPt s₀ U ≫ i ≫ _ = affPt s₀ U ≫ j
    rw [← Category.assoc, show affPt s₀ U ≫ i = _ from (hX.red (op U)).symm,
      show affPt s₀ U ≫ j = _ from (hY.red (op U)).symm, Category.assoc]
    change spMap (S'.p (op U)) ≫ 𝒰.f U ≫ _ = _
    rw [𝒰.map_glueMorphismsOfLocallyDirected g hg U]
    change spMap (S'.p (op U)) ≫ spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U) = _
    rw [← Category.assoc, ← spMap_comp₂]
    exact congrArg (· ≫ hY.y (op U)) (congrArg spMap (RingHom.ext fun b ↦ hψp (op U) b))

end GlobalTheory.LiftSys.Glue
