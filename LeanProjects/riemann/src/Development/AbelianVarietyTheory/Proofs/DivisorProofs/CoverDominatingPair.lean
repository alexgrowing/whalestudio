import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

namespace GlobalTheory.Mean4O.CoverDom

theorem exists_cover_dominating_cover (F : Type) [Field F] [NumberField F] (Y : Var F) (W V : Mean4O.Cover Y)
    (k : W.G ⟶ V.G) (hk : k ≫ V.π = W.π) :
    ∃ (W' : Mean4O.Cover Y) (a : W'.X ⟶ W.X) (b : W'.X ⟶ V.X), a ≫ W.p = W'.p ∧ b ≫ V.p = W'.p ∧
      Lies W' W a ∧ Lies W' V b := by
  have H₀ := W.pb
  have := V.ar.isIntegral
  have := W.ar.isLocallyNoetherian
  have : IsProper W.p := CommonModel.isProper_of_isProjOver W.ar.isProjOver
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  let r := pullback.fst W.p V.p
  have hc : W.j ≫ W.p = (k ≫ V.j) ≫ V.p := by
    rw [W.pb.w, Category.assoc, Category.assoc, V.pb.w, ← hk]; simp only [Category.assoc]
  let h : W.G ⟶ pullback W.p V.p := pullback.lift W.j (k ≫ V.j) hc
  have hr : h ≫ r = W.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd W.p V.p = k ≫ V.j := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ W.p) := GlobalTheory.ProjSpace.isProjOver_pullback W.ar.isProjOver V.ar.isProjOver
  have w : h ≫ r ≫ W.p = (W.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F))
  let f' : W.G ⟶ pullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h (W.π ≫ Y.str) w
  let ρ : pullback (r ≫ W.p) (spMap (algebraMap (𝓞 F) F)) ⟶ W.G :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ W.π ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 W.G := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ W.π ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ (W.π ≫ Y.str)
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ W.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ W.p) F (W.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme W.G := isNormalScheme_G W
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat W.j := MorphismProperty.of_isPullback W.pb.flip ‹_›
  have : IsPreimmersion W.j := MorphismProperty.of_isPullback W.pb.flip ‹_›
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = W.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd W.p V.p = k ≫ V.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := ModelDom.exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) W.j e₁
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
      (h.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← W.ar.dim_eq]
    exact (ModelDom.dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ W.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ W.p) (W.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  let W' : Mean4O.Cover Y :=
    { X := h.normalization
      p := h.fromNormalization ≫ r ≫ W.p
      ar := ⟨W.ar.isDomain, W.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := W.G
      j := h.toNormalization
      π := W.π
      pb := hpb'
      φ := W.φ
      φ_spec := W.φ_spec }
  refine ⟨W', h.fromNormalization ≫ r, h.fromNormalization ≫ pullback.snd W.p V.p, Category.assoc _ _ _, ?_,
    ⟨𝟙 W.G, by rw [Category.id_comp]; exact e₁.symm, Category.id_comp _⟩, ⟨k, e₂.symm, hk⟩⟩
  change (h.fromNormalization ≫ pullback.snd W.p V.p) ≫ V.p = h.fromNormalization ≫ r ≫ W.p
  rw [Category.assoc, ← pullback.condition]

end GlobalTheory.Mean4O.CoverDom
