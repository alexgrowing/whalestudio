import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteLift

theorem exists_retraction {V B : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing B]
    (φ : V →+* B) (hφ : φ.IsIntegral) (ψ : B →+* FractionRing V)
    (h : ψ.comp φ = algebraMap V (FractionRing V)) :
    ∃ s : B →+* V, s.comp φ = RingHom.id V ∧ (algebraMap V (FractionRing V)).comp s = ψ := by
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  have hmem : ∀ b, ψ b ∈ (algebraMap V (FractionRing V)).range := by
    intro b
    obtain ⟨p, hp, hpb⟩ := hφ b
    have : IsIntegral V (ψ b) := ⟨p, hp, by rw [← h, ← Polynomial.hom_eval₂, hpb, map_zero]⟩
    exact IsIntegrallyClosed.algebraMap_eq_of_integral this
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  have key : ∀ b, algebraMap V (FractionRing V) (e.symm (ψ.codRestrict _ hmem b)) = ψ b := fun b =>
    congrArg Subtype.val (e.apply_symm_apply (ψ.codRestrict _ hmem b))
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), ?_, ?_⟩
  · ext v
    apply hinj
    exact (key (φ v)).trans (DFunLike.congr_fun h v)
  · ext b
    exact key b

theorem exists_lift {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    {X Z : Scheme.{0}} (π : X ⟶ Z) [IsFinite π] (f : Sp V ⟶ Z) (y : Sp (FractionRing V) ⟶ X)
    (h : y ≫ π = jK V ≫ f) : ∃ l : Sp V ⟶ X, l ≫ π = f ∧ jK V ≫ l = y := by
  have : IsAffine (pullback π f) := isAffine_of_isAffineHom (pullback.snd π f)
  let P := pullback π f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ pullback.snd π f)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pullback.lift y (jK V) h ≫ P.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hfin
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_retraction φ.hom hfin.to_isIntegral ψ.hom
    (congrArg CommRingCat.Hom.hom hc)
  have h1 : Spec.map (CommRingCat.ofHom s) ≫ P.isoSpec.inv ≫ pullback.snd π f = 𝟙 _ := by
    rw [← hφ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext hs1
  have h2 : jK V ≫ Spec.map (CommRingCat.ofHom s) =
      pullback.lift y (jK V) h ≫ P.isoSpec.hom := by
    rw [← hψ, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hs2
  refine ⟨Spec.map (CommRingCat.ofHom s) ≫ P.isoSpec.inv ≫ pullback.fst π f, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h1]
  · rw [reassoc_of% h2, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _

theorem exists_stalk_lift : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsIntegrallyClosed V₁ → ∀ (X Z : Scheme.{0}) (π : X ⟶ Z), IsFinite π → ∀ (f : Sp V₁ ⟶ Z) (yM : Sp (FractionRing V₁) ⟶ X), yM ≫ π = jK V₁ ≫ f → ∃ (z₁ : X) (ev : X.presheaf.stalk z₁ →+* V₁), IsLocalHom ev ∧ spMap ev ≫ X.fromSpecStalk z₁ ≫ π = f ∧ jK V₁ ≫ spMap ev ≫ X.fromSpecStalk z₁ = yM := by
  intro V _ _ _ hV X Z π hπ f y h
  obtain ⟨l, h1, h2⟩ := exists_lift π f y h
  have e : spMap (Scheme.stalkClosedPointTo (R := .of V) l).hom ≫ X.fromSpecStalk _ = l :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of V) l
  refine ⟨_, (Scheme.stalkClosedPointTo (R := .of V) l).hom, inferInstance, ?_, ?_⟩
  · rw [reassoc_of% e, h1]
  · rw [e, h2]

end GlobalTheory.FiniteLift
