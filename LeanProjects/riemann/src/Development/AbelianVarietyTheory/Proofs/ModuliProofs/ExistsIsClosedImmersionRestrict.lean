import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.FiniteImage

open GlobalTheory.DenseFibreIso

theorem exists_isClosedImmersion_restrict {R : Type} [CommRing R] {U Z : Scheme.{0}}
    (s : Z ⟶ Sp R) (u : U ⟶ Z) [IsFinite u] (K : Type) [Field K] [Algebra R K]
    (hc : IsClosedImmersion (pullback.snd u (pullback.fst s (spMap (algebraMap R K)))))
    (x : Z) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    ∃ V : Z.Opens, x ∈ V ∧ IsClosedImmersion (u ∣_ V) := by
  obtain ⟨A, B, ψ, φ, j, j', _, ⟨y, rfl⟩, H, hj⟩ := exists_chart s u x
  let : Algebra R A := ψ.hom.toAlgebra
  let : Algebra A B := φ.hom.toAlgebra
  replace H : IsPullback (spMap (algebraMap A B)) j' j u := H
  replace hj : j ≫ s = spMap (algebraMap R A) := hj
  have H₁ := isPullback_tensor R A K
  obtain ⟨m, hm, -⟩ := Scheme.exists_preimage_of_isPullback H₁ y (⊥ : PrimeSpectrum K) (by
    rw [← hj, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.ext hx.symm)
  have H₂ := (isPullback_tensor A (A ⊗[R] K) B).paste_vert H
  have H₀ := (IsPullback.of_hasPullback u (pullback.fst s (spMap (algebraMap R K)))).flip
  have hw : (spMap (algebraMap A (A ⊗[R] K)) ≫ j) ≫ s =
      spMap (Algebra.TensorProduct.includeRight.toRingHom : K →+* A ⊗[R] K) ≫
        spMap (algebraMap R K) := by
    rw [Category.assoc, hj]; exact H₁.w
  have e : pullback.lift _ _ hw ≫ pullback.fst s _ = _ := pullback.lift_fst _ _ _
  have H₃ := IsPullback.of_bot' (v₁₂ := pullback.lift _ _ hw) (by rw [e]; exact H₂) H₀
  have hi := MorphismProperty.of_isPullback (P := @IsClosedImmersion) H₃.flip hc
  have hs : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B) := by
    have h2 := (IsClosedImmersion.isAffine_surjective_of_isAffine (spMap
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))).2
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : (A ⊗[R] K) →+* (A ⊗[R] K) ⊗[A] B))
    have h3 := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ((A ⊗[R] K) ⊗[A] B))).hom).2.comp h2
    rw [← ConcreteCategory.coe_comp, e, ConcreteCategory.coe_comp] at h3
    exact h3.of_comp
  have h1 : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H.flip ‹_›
  have : Module.Finite A B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1 h1)
  obtain ⟨a, ha, ha'⟩ := exists_away_surjective (A ⊗[R] K) hs m
  have hQ := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom _) ha'
  have H₄ := (isPullback_tensor A (Localization.Away a) B).paste_vert H
  let g := spMap (algebraMap A (Localization.Away a)) ≫ j
  refine ⟨g.opensRange, ?_, ?_⟩
  · have hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a, ← hm]
      exact ha
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, Scheme.Hom.comp_apply _ _ _⟩
  · have H' := H₄.of_iso (Iso.refl _) g.isoOpensRange (Iso.refl _) (Iso.refl _)
      (fst' := _ ≫ g.isoOpensRange.hom) (snd' := _) (f' := g.opensRange.ι) (g' := u)
      (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by simp [g]) (by simp)
    have H'' := isPullback_morphismRestrict u g.opensRange
    rw [← H''.isoIsPullback_hom_fst _ _ H',
      MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
      MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
    exact hQ

theorem restrict_sSup (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {U Z : Scheme.{0}} (u : U ⟶ Z) :
    Q (u ∣_ sSup {V : Z.Opens | Q (u ∣_ V)}) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  obtain ⟨V, hV, hx⟩ := TopologicalSpace.Opens.mem_sSup.1 x.2
  refine ⟨(sSup {V : Z.Opens | Q (u ∣_ V)}).ι ⁻¹ᵁ V, hx, ?_⟩
  rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict _ _ _)]
  refine (Q.arrow_mk_iso_iff (morphismRestrictEq u ?_)).2 hV
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.2 (le_sSup hV)

theorem dense_of_flat {O : Type} [CommRing O] [IsDomain O] {T : Scheme.{0}} (t : T ⟶ Sp O)
    [Flat t] (W : Set T) (hW : ∀ x : T, (t x).asIdeal = ⊥ → x ∈ W) : Dense W := by
  intro x
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) ⤳ t x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal O) ≤ _ from bot_le)
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap t hsp
  exact hy.mem_closed isClosed_closure (subset_closure (hW y (by rw [hy'])))

theorem main : ∀ (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F] (U Z : Scheme.{0}) (u : U ⟶ Z) (s : Z ⟶ Sp O), IsFinite u → IsReduced U → Flat (u ≫ s) → LocallyOfFiniteType s → QuasiCompact s → IsClosedImmersion (pullback.snd u (pullback.fst s (spMap (algebraMap O F)))) → ∃ (XX : Scheme.{0}) (u' : U ⟶ XX) (i : XX ⟶ Z) (W : XX.Opens), u' ≫ i = u ∧ IsClosedImmersion i ∧ IsFinite u' ∧ Surjective u' ∧ Dense (W : Set XX) ∧ IsIso (u' ∣_ W) ∧ Dense ((u' ⁻¹ᵁ W : U.Opens) : Set U) ∧ IsReduced XX ∧ Flat (i ≫ s) := by
  intro O F _ _ _ _ _ U Z u s _ _ _ _ _ hc
  let W₀ : Z.Opens := sSup {V : Z.Opens | IsClosedImmersion (u ∣_ V)}
  have hW₀ : IsClosedImmersion (u ∣_ W₀) := restrict_sSup @IsClosedImmersion u
  have hmem : ∀ z : Z, (s z).asIdeal = ⊥ → z ∈ W₀ := fun z hz => by
    obtain ⟨V, hV, hV'⟩ := exists_isClosedImmersion_restrict s u F hc z (by
      rw [hz]; exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O F))
    exact TopologicalSpace.Opens.mem_sSup.2 ⟨V, hV', hV⟩
  have hfl : Flat (u.imageι ≫ s) := flat_image_of_isDedekindDomain (O := CommRingCat.of O) u s
  have : IsFinite (u.toImage ≫ u.imageι) := by rw [u.toImage_imageι]; infer_instance
  have hfin : IsFinite u.toImage := IsFinite.of_comp _ u.imageι
  refine ⟨u.image, u.toImage, u.imageι, u.imageι ⁻¹ᵁ W₀, u.toImage_imageι, inferInstance, hfin,
    surjective_of_isDominant_of_isClosed_range _ u.toImage.isClosedMap.isClosed_range,
    dense_of_flat (u.imageι ≫ s) _ fun x hx => hmem _ (by rwa [← Scheme.Hom.comp_apply]), ?_,
    dense_of_flat (u ≫ s) _ fun x hx => ?_, inferInstance, hfl⟩
  · have h1 : IsClosedImmersion ((u.toImage ≫ u.imageι) ∣_ W₀) := by
      have : ∀ v : U ⟶ Z, v = u → IsClosedImmersion (v ∣_ W₀) := by rintro _ rfl; exact hW₀
      exact this _ u.toImage_imageι
    rw [morphismRestrict_comp] at h1
    have h2 : IsClosedImmersion (u.toImage ∣_ u.imageι ⁻¹ᵁ W₀) :=
      @IsClosedImmersion.of_comp _ _ _ _ (u.imageι ∣_ W₀) h1 _
    have h3 : IsSchemeTheoreticallyDominant (u.toImage ∣_ u.imageι ⁻¹ᵁ W₀) :=
      IsSchemeTheoreticallyDominant.of_isPullback
        (isPullback_morphismRestrict u.toImage (u.imageι ⁻¹ᵁ W₀)).flip
    exact isIso_of_isClosedImmersion_of_schemeDominant _
  · change u.imageι (u.toImage x) ∈ W₀
    rw [← Scheme.Hom.comp_apply, u.toImage_imageι]
    exact hmem _ (by rwa [← Scheme.Hom.comp_apply])

end GlobalTheory.FiniteImage
