import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

theorem exists_isPullback_spec_of_isFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (D : CommRingCat.{0})
    (e : Spec D ⟶ Y) :
    ∃ (H : CommRingCat.{0}) (φ : D ⟶ H) (y : Spec H ⟶ X), φ.hom.Finite ∧ IsPullback y (Spec.map φ) f e := by
  have : IsAffine (pullback f e) := isAffine_of_isAffineHom (pullback.snd f e)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((pullback f e).isoSpec.inv ≫ pullback.snd f e)
  refine ⟨_, φ, (pullback f e).isoSpec.inv ≫ pullback.fst f e, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  · rw [hφ]
    exact (IsPullback.of_hasPullback f e).of_iso (pullback f e).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)

theorem eq_of_forall_nilpotent_aug {Ω O : Type} [Field Ω] [IsAlgClosed Ω] [CommRing O] [Algebra Ω O]
    [Module.Finite Ω O] {a b : O}
    (h : ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
      ∀ g : O →ₐ[Ω] A, g a = g b) : a = b := by
  have : IsArtinianRing O := IsArtinianRing.of_finite Ω O
  refine sub_eq_zero.1 (eq_zero_of_localization _ fun q hq => ?_)
  rw [map_sub, sub_eq_zero]
  let A := Localization.AtPrime q
  let g : O →ₐ[Ω] A := IsScalarTower.toAlgHom Ω O A
  have hg : Function.Surjective g := IsArtinianRing.localization_surjective q.primeCompl A
  have : Module.Finite Ω A := Module.Finite.of_surjective g.toLinearMap hg
  have : IsArtinianRing A := IsArtinianRing.of_finite Ω A
  let r : A →ₐ[Ω] ResidueField A := IsScalarTower.toAlgHom Ω A (ResidueField A)
  have : Module.Finite Ω (ResidueField A) := Module.Finite.of_surjective r.toLinearMap residue_surjective
  let e : Ω ≃ₐ[Ω] ResidueField A :=
    AlgEquiv.ofBijective (Algebra.ofId Ω _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine h A (e.symm.toAlgHom.comp r) ?_ g
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  refine ⟨N, le_bot_iff.1 (le_trans (Ideal.pow_right_mono ?_ N) hN.le)⟩
  rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  intro t ht
  have : e.symm (r t) = 0 := ht
  exact (residue_eq_zero_iff t).1 ((map_eq_zero_iff _ e.symm.injective).1 this)

theorem cubWeil_one_of_local_artinian : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (n : ℕ), IsFinite ((𝟙 G) ^ n : G ⟶ G).left → ∀ (D : Type) [CommRing D] [Algebra Ω D] [Module.Finite Ω D] (x : overAt s D ⟶ G), x ^ n = 1 → (∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ (f : D →ₐ[Ω] A) (y : overAt s A ⟶ G), y ^ n = 1 → CubWeil c n (homAt s f ≫ x) y 1) → ∀ (T' : Over S) (ρ : T' ⟶ overAt s D) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1 := by
  intro Ω _ _ S s G _ _ L c n hfin D _ _ _ x hx h T' ρ y hy
  obtain ⟨H, φ, y₀, hφ, hpb⟩ := exists_isPullback_spec_of_isFinite ((𝟙 G) ^ n : G ⟶ G).left (CommRingCat.of D)
    (1 : overAt s D ⟶ G).left
  let : Algebra D H := φ.hom.toAlgebra
  let : Algebra Ω H := (φ.hom.comp (algebraMap Ω D)).toAlgebra
  have : IsScalarTower Ω D H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite D H := hφ
  have : Module.Finite Ω H := Module.Finite.trans D H
  let j : D →ₐ[Ω] H := IsScalarTower.toAlgHom Ω D H
  have hj : (homAt s j).left = Spec.map φ := rfl
  have hpow : ∀ {T : Over S} (z : T ⟶ G), z.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = (z ^ n).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {T : Over S} (r : T ⟶ overAt s D), r.left ≫ (1 : overAt s D ⟶ G).left = (1 : T ⟶ G).left := by
    intro T r
    rw [← Over.comp_left, MonObj.comp_one]
  have hw : y₀ ≫ G.hom = (overAt s H).hom := by
    rw [← Over.w ((𝟙 G) ^ n : G ⟶ G), ← Category.assoc, hpb.w, Category.assoc, Over.w (1 : overAt s D ⟶ G)]
    exact Over.w (homAt s j)
  let u : overAt s H ⟶ G := Over.homMk y₀ hw
  have hu : u ^ n = 1 := Over.OverMorphism.ext (by rw [← hpow, ← hone (homAt s j)]; exact hpb.w)
  have hx' : (homAt s j ≫ x) ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c hx' hu
  have hζ1 : ζ = 1 := by
    refine Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of H)).hom).1 ?_)
    refine eq_of_forall_nilpotent_aug (Ω := Ω) fun A _ _ π hπ g => ?_
    have h₁ := h A π hπ (g.comp j) (homAt s g ≫ u) (by rw [← MonObj.comp_pow, hu, MonObj.comp_one])
    rw [← hom_comp, Category.assoc] at h₁
    have e : (homAt s g).left.appTop.hom ζ.val = (homAt s g).left.appTop.hom (1 : Γ((overAt s H).left, ⊤)ˣ).val :=
      (congrArg Units.val ((hζ.comp (homAt s g)).unique h₁)).trans (map_one _).symm
    have nat := fun t => congrArg (fun q => q.hom t) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (g : H →+* A)))
    exact (nat _).symm.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom e).trans (nat _))
  subst hζ1
  have hl : y.left ≫ ((𝟙 G) ^ n : G ⟶ G).left = ρ.left ≫ (1 : overAt s D ⟶ G).left := by rw [hpow, hy, hone]
  let l : T' ⟶ overAt s H := Over.homMk (hpb.lift _ _ hl) (by
    rw [← Over.w (homAt s j), hj, ← Over.w ρ]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hpb.lift_snd _ _ hl)))
  have e₁ : l ≫ homAt s j = ρ := Over.OverMorphism.ext (hpb.lift_snd _ _ hl)
  have e₂ : l ≫ u = y := Over.OverMorphism.ext (hpb.lift_fst _ _ hl)
  have := hζ.comp l
  rwa [← Category.assoc, e₁, e₂, map_one] at this

end GlobalTheory.AlphaPair
