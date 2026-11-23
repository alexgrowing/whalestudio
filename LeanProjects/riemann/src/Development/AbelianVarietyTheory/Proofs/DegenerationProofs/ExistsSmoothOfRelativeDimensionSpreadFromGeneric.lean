import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOpensSmoothOfRelativeDimensionOfFlat
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenSpread

theorem isIso_stalkMap_of_flat {X Y : Scheme.{0}} (φ : X ⟶ Y) [Flat φ] [SurjectiveOnStalks φ] (x : X) :
    IsIso (φ.stalkMap x) := by
  have h1 := Flat.stalkMap φ x
  have h2 := φ.stalkMap_surjective x
  algebraize [(φ.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (φ.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (φ x))
    (B := X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (φ x)) (X.presheaf.stalk x), h2⟩

theorem mem_smoothLocus_of_isPullback {X X₀ S S₀ : Scheme.{0}} {f : X ⟶ S} {f₀ : X₀ ⟶ S₀}
    {φ : X₀ ⟶ X} {j : S₀ ⟶ S} (h : IsPullback φ f₀ f j) [LocallyOfFinitePresentation f] [Flat j]
    [SurjectiveOnStalks j] [Smooth f₀] (x : X₀) : φ x ∈ f.smoothLocus := by
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  have : SurjectiveOnStalks φ :=
    MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) h.flip inferInstance
  have := isIso_stalkMap_of_flat φ x
  have := isIso_stalkMap_of_flat j (f₀ x)
  have h0 : (f₀.stalkMap x).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (f₀.smoothLocus_eq_top.ge (Set.mem_univ x))
  have h1 : ((f₀ ≫ j).stalkMap x).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).2 h0
  rw [← h.w, Scheme.Hom.stalkMap_comp] at h1
  exact Scheme.Hom.mem_smoothLocus.mpr
    ((RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).1 h1)

theorem exists_opens_smoothOfRelativeDimension_of_isPullback {X X₀ S S₀ : Scheme.{0}} {f : X ⟶ S}
    {f₀ : X₀ ⟶ S₀} {φ : X₀ ⟶ X} {j : S₀ ⟶ S} (h : IsPullback φ f₀ f j)
    [LocallyOfFinitePresentation f] [Flat j] [SurjectiveOnStalks j] (n : ℕ)
    [SmoothOfRelativeDimension n f₀] (x : X₀) :
    ∃ W : X.Opens, φ x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by
  have : Smooth f₀ := SmoothOfRelativeDimension.smooth n _
  have hz := mem_smoothLocus_of_isPullback h x
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have h1 : SmoothOfRelativeDimension (0 + n) (pullback.snd f j) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  have h2 : SmoothOfRelativeDimension (0 + (0 + (0 + n))) (pullback.snd (f.smoothLocus.ι ≫ f) j) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨W, hW, hW'⟩ := GlobalTheory.VeryDenseFibres.exists_opens_smoothOfRelativeDimension
    (f.smoothLocus.ι ≫ f) j n (by simpa using h2) ⟨φ x, hz⟩ (f₀ x) (by
      change f (φ x) = _
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w])
  let i := W.ι ≫ f.smoothLocus.ι
  refine ⟨i.opensRange, ⟨⟨⟨φ x, hz⟩, hW⟩, rfl⟩, ?_⟩
  have e : i.opensRange.ι ≫ f = i.isoOpensRange.inv ≫ (W.ι ≫ f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, Category.assoc]
  have h3 : SmoothOfRelativeDimension (0 + n)
      (i.isoOpensRange.inv ≫ (W.ι ≫ f.smoothLocus.ι ≫ f)) := inferInstance
  rw [e]
  simpa using h3

theorem exists_smoothOfRelativeDimension :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → IsProper f → SmoothOfRelativeDimension n f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → SmoothOfRelativeDimension n f' := by
  intro R K _ _ _ _ _ _ n X X₀ f f₀ φ h hf hf₀
  have : LocallyOfFinitePresentation f := inferInstance
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  let U : X.Opens := ⨆ W : {W : X.Opens // SmoothOfRelativeDimension n (W.ι ≫ f)}, W.1
  have hc : IsClosed (f '' (U : Set X)ᶜ) := f.isClosedMap _ U.2.isClosed_compl
  obtain ⟨a, ha, H⟩ := exists_forall_notMem (K := K) hc (by
    rintro w ⟨z, hz, e⟩
    obtain ⟨x, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h z w e
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_isPullback h n x
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have h1 : SmoothOfRelativeDimension n (pullback.snd f (spMap g)) := by
    refine GlobalTheory.ProperFlatNearFibre.smoothOfRelativeDimension_pullback_snd _ _ n fun z y e => ?_
    have h2 : z ∈ U := by
      by_contra hz
      exact H R' g hg y ⟨z, hz, e⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩
  have h2 : SmoothOfRelativeDimension (0 + n) (hp.isoPullback.hom ≫ pullback.snd f (spMap g)) :=
    inferInstance
  simpa using h2

end GlobalTheory.GenSpread
