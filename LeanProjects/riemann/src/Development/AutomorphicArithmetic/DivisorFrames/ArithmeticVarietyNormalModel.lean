import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

theorem UpperTheory.arithmetic_variety_normal_model :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (T : Scheme.{0}) (sT : T ⟶ Sp (𝓞 F)) (ρ : V.G ⟶ T), IsProjOver sT → ρ ≫ sT = (V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) → ∃ (X : Scheme.{0}) (_ : IsIntegral X) (j : V.G ⟶ X) (a : X ⟶ V.X) (b : X ⟶ T), IsArithVar (a ≫ V.p) Y.dim ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X ∧ IsPullback j (V.π ≫ Y.str) (a ≫ V.p) (spMap (algebraMap (𝓞 F) F)) ∧ j ≫ a = V.j ∧ j ≫ b = ρ ∧ Surjective a := by
  intro F _ _ Y V T sT ρ hT hρT
  have H₀ := V.pb
  have := V.ar.isLocallyNoetherian
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : IsProper sT := CommonModel.isProper_of_isProjOver hT
  have : IsProper (V.π ≫ Y.str) := MorphismProperty.of_isPullback V.pb ‹IsProper V.p›
  let r := pullback.fst V.p sT
  let h : V.G ⟶ pullback V.p sT := pullback.lift V.j ρ (V.pb.w.trans hρT.symm)
  have hr : h ≫ r = V.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd V.p sT = ρ := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ V.p) := GlobalTheory.ProjSpace.isProjOver_pullback V.ar.isProjOver hT
  have w : h ≫ r ≫ V.p = (V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))
  let f' : V.G ⟶ pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h (V.π ≫ Y.str) w
  let ρ' : pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) ⟶ V.G :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ' ≫ (V.π ≫ Y.str) = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ' = 𝟙 V.G := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ' ≫ (V.π ≫ Y.str)) := by rw [hρ]; infer_instance
  have : IsSeparated ρ' := IsSeparated.of_comp ρ' (V.π ≫ Y.str)
  have : IsClosedImmersion (f' ≫ ρ') := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ'
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ V.p) F (V.π ≫ Y.str) w
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : GlobalTheory.IsNormalScheme V.G := GlobalTheory.IsNormalScheme.of_pred fun x => by
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks V.j x
    have := (V.normal (V.j x)).2
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv (asIso (V.j.stalkMap x)).commRingCatIsoToRingEquiv⟩
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = V.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd V.p sT = ρ := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  obtain ⟨U, hne, _⟩ := GlobalTheory.ModelDom.exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) V.j e₁
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
  have hsurj := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
    (h.fromNormalization ≫ r).isClosedMap.isClosed_range
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    rw [← V.ar.dim_eq]
    exact (GlobalTheory.ModelDom.dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ V.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ V.p) (V.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  refine ⟨h.normalization, hint, h.toNormalization, h.fromNormalization ≫ r,
    h.fromNormalization ≫ pullback.snd V.p sT, ?_, GlobalTheory.IsNormalScheme.pred _, ?_, e₁, e₂, hsurj⟩
  · rw [Category.assoc]
    exact ⟨V.ar.isDomain, V.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩
  · rw [Category.assoc]
    exact hpb'
