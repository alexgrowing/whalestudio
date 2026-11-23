import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ChartModel

set_option backward.isDefEq.respectTransparency false

noncomputable def twoCover {X U V : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) : X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun i => Bool.rec U V i)
    (fun i => Bool.rec (motive := fun i => (Bool.rec U V i : Scheme.{0}) ⟶ X) u v i) (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩) (fun i => by cases i <;> assumption)

theorem isClosedImmersion_snd_diagonal {U Y S : Scheme.{0}} (g : U ⟶ Y) (f : Y ⟶ S) [Mono g]
    [IsSeparated (g ≫ f)] :
    IsClosedImmersion (pullback.snd (pullback.diagonal f)
      (pullback.map (g ≫ f) (g ≫ f) f f g g (𝟙 _) (Category.comp_id _) (Category.comp_id _))) := by
  have H := pullback_map_diagonal_isPullback g g f
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom,
    H.isoPullback_hom_snd, ← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.diagonal g)]
  convert (inferInstance : IsClosedImmersion (pullback.diagonal (g ≫ f)))
  ext : 1 <;> simp

theorem isSeparated_of_two {U V Y S : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion u]
    [IsOpenImmersion v] [IsSeparated (u ≫ f)] [IsSeparated (v ≫ f)]
    (h : ∀ x y : Y, f x = f y → (x ∈ Set.range u ∧ y ∈ Set.range u) ∨ (x ∈ Set.range v ∧ y ∈ Set.range v)) :
    IsSeparated f := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (twoCover
    (pullback.map (u ≫ f) (u ≫ f) f f u u (𝟙 _) (Category.comp_id _) (Category.comp_id _))
    (pullback.map (v ≫ f) (v ≫ f) f f v v (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ?_) ?_
  · intro z
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_map]
    exact h _ _ (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
  · rintro (_ | _)
    · exact isClosedImmersion_snd_diagonal u f
    · exact isClosedImmersion_snd_diagonal v f

theorem exists_glue_chart {S T A X W : Scheme.{0}} (i : T ⟶ S) [IsOpenImmersion i] (a : A ⟶ T) (c : X ⟶ S)
    {p : W ⟶ X} {w : W ⟶ T} (hW : IsPullback p w c i) (u : W ⟶ A) [IsOpenImmersion u] (hu : u ≫ a = w)
    [Smooth a] [IsSeparated a] [Smooth c] [IsSeparated c] [CompactSpace A] [CompactSpace X] :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (g : X ⟶ Y) (j : A ⟶ Y), IsOpenImmersion g ∧ IsPullback j a f i ∧ g ≫ f = c ∧
      p ≫ g = u ≫ j ∧ Smooth f ∧ IsSeparated f ∧ CompactSpace Y ∧ ∀ y, f y ∉ Set.range i → y ∈ Set.range g := by
  have : IsOpenImmersion p := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hW.flip ‹_›
  have := GlueModels.isOpenImmersion_inl p u
  have := GlueModels.isOpenImmersion_inr p u
  have hc := GlueModels.pushout_cover p u
  let f : pushout p u ⟶ S := pushout.desc c (a ≫ i) (by rw [hW.w, ← Category.assoc, hu])
  have h1 : pushout.inl p u ≫ f = c := pushout.inl_desc _ _ _
  have h2 : pushout.inr p u ≫ f = a ≫ i := pushout.inr_desc _ _ _
  have e1 (x : X) : f (pushout.inl p u x) = c x := congrArg (fun g => g x) h1
  have e2 (x : A) : f (pushout.inr p u x) = i (a x) := congrArg (fun g => g x) h2
  have e3 (x : W) : pushout.inl p u (p x) = pushout.inr p u (u x) :=
    congrArg (fun g => g x) (pushout.condition (f := p) (g := u))
  have hin (y) (hy : f y ∈ Set.range i) : y ∈ Set.range (pushout.inr p u) := by
    rcases hc y with ⟨x, rfl⟩ | hy
    · obtain ⟨t, ht⟩ := hy
      obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hW x t ((e1 x).symm.trans ht.symm)
      exact ⟨u z, (e3 z).symm⟩
    · exact hy
  have hout (y) (hy : f y ∉ Set.range i) : y ∈ Set.range (pushout.inl p u) := by
    rcases hc y with h | ⟨x, rfl⟩
    · exact h
    · exact absurd ⟨a x, (e2 x).symm⟩ hy
  refine ⟨_, f, pushout.inl p u, pushout.inr p u, inferInstance, ?_, h1, pushout.condition, ?_, ?_, ?_, hout⟩
  · refine (IsOpenImmersion.isPullback _ _ _ _ h2 ?_).flip
    ext y
    constructor
    · exact hin y
    · rintro ⟨x, rfl⟩
      exact ⟨a x, (e2 x).symm⟩
  · refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (twoCover _ _ hc) ?_
    rintro (_ | _)
    · change Smooth (pushout.inl p u ≫ f)
      rw [h1]; infer_instance
    · change Smooth (pushout.inr p u ≫ f)
      rw [h2]; infer_instance
  · have : IsSeparated (pushout.inl p u ≫ f) := by rw [h1]; infer_instance
    have : IsSeparated (pushout.inr p u ≫ f) := by rw [h2]; infer_instance
    refine isSeparated_of_two (pushout.inl p u) (pushout.inr p u) f fun x y hxy => ?_
    by_cases hx : f x ∈ Set.range i
    · exact Or.inr ⟨hin x hx, hin y (hxy ▸ hx)⟩
    · exact Or.inl ⟨hout x hx, hout y (hxy ▸ hx)⟩
  · refine ⟨?_⟩
    rw [← Set.eq_univ_of_forall (s := Set.range (pushout.inl p u) ∪ Set.range (pushout.inr p u)) hc]
    exact (isCompact_range (pushout.inl p u).continuous).union (isCompact_range (pushout.inr p u).continuous)

theorem exists_model_of_chart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∀ (C : Type) [CommRing C] [Algebra R C], Algebra.Smooth R C → ∀ u : Sp (TensorProduct R K C) ⟶ A.left, IsOpenImmersion u → u ≫ A.hom = spMap (algebraMap K (TensorProduct R K C)) → ∃ (M : Model R A) (g : Sp C ⟶ M.Y.left), IsOpenImmersion g ∧ g ≫ M.Y.hom = spMap (algebraMap R C) ∧ spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom ≫ g = u ≫ M.j ∧ M.sp ⊆ Set.range g := by
  intro R K _ _ _ _ _ _ A hA hs hq C _ _ hC u hu hua
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hloc : IsLocalization.Away π K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (S := K) (M := Submonoid.powers π) (nonZeroDivisors R)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) fun r hr => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hr) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
  have hi : IsOpenImmersion (spMap (algebraMap R K)) := IsOpenImmersion.of_isLocalization π
  have hW : IsPullback (spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom)
      (spMap (algebraMap K (TensorProduct R K C))) (spMap (algebraMap R C)) (spMap (algebraMap R K)) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K C)).flip
  have : Smooth (spMap (algebraMap R C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hC
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨Y, f, g, j, hg, hj, hgf, hp, h1, h2, h3, h4⟩ :=
    exists_glue_chart (spMap (algebraMap R K)) A.hom (spMap (algebraMap R C)) hW u hua
  refine ⟨⟨Over.mk f, Over.isoMk hj.isoPullback.symm hj.isoPullback_inv_snd, h1, h2,
    (inferInstance : QuasiCompact f)⟩, g, hg, hgf, ?_, fun y hy => h4 y ?_⟩
  · exact hp.trans (congrArg (u ≫ ·) hj.isoPullback_hom_fst.symm)
  · rintro ⟨t, ht⟩
    have ht' : spMap (algebraMap R K) t = IsLocalRing.closedPoint R := ht.trans hy
    have h5 : π ∈ (spMap (algebraMap R K) t).asIdeal := by
      rw [ht']; exact hπ.not_isUnit
    exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show algebraMap R K π ∈ t.asIdeal from h5)
      (IsLocalization.Away.algebraMap_isUnit π))

end GlobalTheory.ChartModel
