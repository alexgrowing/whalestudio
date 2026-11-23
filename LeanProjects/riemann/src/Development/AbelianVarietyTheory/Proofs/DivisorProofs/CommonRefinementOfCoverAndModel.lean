import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

namespace GlobalTheory.Mean4O.CoverDom

theorem isNormalScheme_G {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) : GlobalTheory.IsNormalScheme V.G := by
  have : GlobalTheory.IsNormalScheme V.X := GlobalTheory.IsNormalScheme.of_pred V.normal
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : ∀ x, IsIso (V.j.stalkMap x) := fun x => isIso_stalkMap_of_flat_of_surjectiveOnStalks V.j x
  exact GlobalTheory.IsNormalScheme.of_isIso_stalkMap V.j

theorem exists_cover_dominating (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y)
    (M : TrueGeo.Model Y) : ∃ (V' : Cover Y) (a : V'.X ⟶ V.X) (g : V'.G ⟶ V.G) (b : V'.X ⟶ M.X),
      a ≫ V.p = V'.p ∧ b ≫ M.p = V'.p ∧ V'.j ≫ a = g ≫ V.j ∧ g ≫ V.π = V'.π ∧
      g (genericPoint V'.G) = genericPoint V.G ∧ V'.j ≫ b = V'.π ≫ M.j := by
  have H₀ := V.pb
  have := M.ar.isIntegral
  have := V.ar.isLocallyNoetherian
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  let r := pullback.fst V.p M.p
  have hc : V.j ≫ V.p = (V.π ≫ M.j) ≫ M.p := by
    rw [V.pb.w, Category.assoc, Category.assoc, M.pb.w]
  let h : V.G ⟶ pullback V.p M.p := pullback.lift V.j (V.π ≫ M.j) hc
  have hr : h ≫ r = V.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd V.p M.p = V.π ≫ M.j := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ V.p) := GlobalTheory.ProjSpace.isProjOver_pullback V.ar.isProjOver M.ar.isProjOver
  have w : h ≫ r ≫ V.p = (V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))
  let f' : V.G ⟶ pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h (V.π ≫ Y.str) w
  let ρ : pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) ⟶ V.G :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ V.π ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 V.G := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ V.π ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ (V.π ≫ Y.str)
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ V.p) F (V.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme V.G := isNormalScheme_G V
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = V.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd V.p M.p = V.π ≫ M.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := ModelDom.exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) V.j e₁
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
      (h.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← V.ar.dim_eq]
    exact (ModelDom.dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ V.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ V.p) (V.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  let V' : Cover Y :=
    { X := h.normalization
      p := h.fromNormalization ≫ r ≫ V.p
      ar := ⟨V.ar.isDomain, V.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := V.G
      j := h.toNormalization
      π := V.π
      pb := hpb'
      φ := V.φ
      φ_spec := V.φ_spec }
  refine ⟨V', h.fromNormalization ≫ r, 𝟙 V.G, h.fromNormalization ≫ pullback.snd V.p M.p, Category.assoc _ _ _, ?_,
    e₁.trans (Category.id_comp _).symm, Category.id_comp _, rfl, e₂⟩
  change (h.fromNormalization ≫ pullback.snd V.p M.p) ≫ M.p = h.fromNormalization ≫ r ≫ V.p
  rw [Category.assoc, ← pullback.condition]

end GlobalTheory.Mean4O.CoverDom
