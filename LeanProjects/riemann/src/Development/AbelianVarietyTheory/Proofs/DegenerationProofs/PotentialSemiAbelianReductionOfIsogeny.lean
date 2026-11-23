import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueFieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HenselianIUnionCompleteOfIntegralOverCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProjByBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.Isog

open IsLocalRing

theorem spMap_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := GlobalTheory.ModelDescent.spMap_comp_eq rfl

theorem isModel_pullback {K W L W' L' : Type} [Field K] [CommRing W] [Field L] [CommRing W'] [Field L']
    [Algebra K L] [Algebra W L] [Algebra K L'] [Algebra W' L'] (c : W →+* W') (b : L →+* L')
    (e : (algebraMap W' L').comp c = b.comp (algebraMap W L)) (e' : b.comp (algebraMap K L) = algebraMap K L')
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (h : IsModel (L := L) A G) :
    IsModel (L := L') A ((Over.pullback (spMap c)).obj G) := by
  obtain ⟨e₀, he₀⟩ := h
  have hW : spMap (algebraMap W' L') ≫ spMap c = spMap b ≫ spMap (algebraMap W L) := by
    rw [spMap_comp, spMap_comp, e]
  have hK : spMap (algebraMap K L') = spMap b ≫ spMap (algebraMap K L) := by
    rw [spMap_comp, e']
  have key : ∀ (φ : Sp L' ⟶ Sp W) (ψ : Sp L' ⟶ Sp K), φ = spMap b ≫ spMap (algebraMap W L) →
      ψ = spMap b ≫ spMap (algebraMap K L) →
      ∃ f : (Over.pullback φ).obj G ≅ (Over.pullback ψ).obj A, IsMonHom f.hom := by
    rintro φ ψ rfl rfl
    refine ⟨pullCompIso _ _ G ≪≫ (Over.pullback (spMap b)).mapIso e₀ ≪≫ (pullCompIso _ _ A).symm, ?_⟩
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    infer_instance
  obtain ⟨f, hf⟩ := key _ _ hW hK
  show ∃ e : _ ≅ _, IsMonHom e.hom
  refine ⟨(pullCompIso _ _ G).symm ≪≫ f, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

theorem pullback_map_id_pow {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (m : ℕ) :
    (Over.pullback f).map (𝟙 B ^ m) = 𝟙 ((Over.pullback f).obj B) ^ m := by
  simpa using map_pow ((Over.pullback f).homMonoidHom) (𝟙 B) m

theorem exists_model_of_isogeny (K R K' : Type) [Field K] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K']
    [Algebra R K'] [Algebra K K'] (hSH : SH R K') (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ)
    (hA : IsAbelianScheme A) (hP : GlobalTheory.AbLaw.IsProjBy A.hom) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (i : A ⟶ B) (r : B ⟶ A) [IsMonHom i] [IsMonHom r] (hm : 1 ≤ m)
    (hri : r ≫ i = 𝟙 _ ^ m) (G' : Over (Sp R)) [GrpObj G'] (hG' : IsSemiAbelian G') (hmod : IsModel (L := K') B G') :
    ∃ (G : Over (Sp R)) (_ : GrpObj G), SmConn G ∧ IsModel (L := K') A G ∧
      Nonempty (TorusExtension (spFibre G)) := by
  obtain ⟨e, he⟩ := hmod
  haveI := he
  have hbc : ∀ (X : Over (Sp K)), SmoothOfRelativeDimension g X.hom →
      SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj X).hom := fun X hX =>
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback X.hom (spMap (algebraMap K K'))) hX
  have hA' : IsAbelianScheme ((Over.pullback (spMap (algebraMap K K'))).obj A) := by
    obtain ⟨h1, h2, h3, h4⟩ := hA
    exact ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd A.hom (spMap (algebraMap K K')))),
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))) h3,
      inferInstanceAs (GeometricallyConnected (pullback.snd A.hom (spMap (algebraMap K K'))))⟩
  have hP' : GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K K'))).obj A).hom :=
    GlobalTheory.AbLaw.isProjBy_baseChange K K' (algebraMap K K') A.left _ A.hom _ _
      (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))) hP
  have hgA' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj A).hom := hbc A hgA
  haveI hgB' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj B).hom := hbc B hgB
  have hgG : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K'))).obj G').hom := by
    haveI : IsIso e.hom.left := ⟨e.inv.left, by simp [← Over.comp_left], by simp [← Over.comp_left]⟩
    have h : SmoothOfRelativeDimension (0 + g) (e.hom.left ≫ ((Over.pullback (spMap (algebraMap K K'))).obj B).hom) := inferInstance
    rw [zero_add, Over.w e.hom] at h
    exact h
  have hri' : (e.hom ≫ (Over.pullback (spMap (algebraMap K K'))).map r) ≫ ((Over.pullback (spMap (algebraMap K K'))).map i ≫ e.inv) = 𝟙 _ ^ m := by
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hri, pullback_map_id_pow, MonObj.pow_comp, MonObj.comp_pow]
    simp
  obtain ⟨G, _, e₂, hsc, he₂, ht⟩ := GlobalTheory.T.semiAbelian_reduction_along_isogeny_strict_henselian R K' hSH ((Over.pullback (spMap (algebraMap K K'))).obj A) G' g m hA' hP' hG' hgA' hgG
    ((Over.pullback (spMap (algebraMap K K'))).map i ≫ e.inv) (e.hom ≫ (Over.pullback (spMap (algebraMap K K'))).map r) inferInstance inferInstance hm hri'
  exact ⟨G, inferInstance, hsc, show ∃ _, _ from ⟨e₂, he₂⟩, ht⟩

end GlobalTheory.SS.Isog

namespace GlobalTheory.SS

open Isog IsLocalRing in

theorem potModel_semiAbelian_of_isogeny : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ A B _ _ g m hA hP hgA hgB i r hi hr hm hri hB
  haveI := hi
  haveI := hr
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hc, hfin, hloc, hcomp, G, _, hmod, hG⟩ := hB
  have hG' : IsSemiAbelian G := hG
  haveI : IsAdicComplete (maximalIdeal W) W := hcomp
  haveI : CharZero L := (RingHom.charZero_iff (algebraMap K L).injective).1 inferInstance
  haveI : CharZero W := (RingHom.charZero_iff (IsFractionRing.injective W L)).2 inferInstance
  haveI : CharZero V := (RingHom.charZero_iff (IsFractionRing.injective V K)).2 inferInstance
  obtain ⟨R, _, _, _, _, hinj, hint, hac⟩ := GlobalTheory.T.exists_integral_ext_isAlgClosed_residueField' W
  obtain ⟨-, hhen, -⟩ := GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr W R hinj hint
  have hWK : Function.Injective ((algebraMap R (FractionRing R)).comp (algebraMap W R)) :=
    (IsFractionRing.injective R (FractionRing R)).comp hinj
  obtain ⟨b, hbW⟩ : ∃ b : L →+* FractionRing R,
      (algebraMap R (FractionRing R)).comp (algebraMap W R) = b.comp (algebraMap W L) :=
    ⟨IsFractionRing.lift hWK, RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := L) hWK x).symm⟩
  letI : Algebra K (FractionRing R) := (b.comp (algebraMap K L)).toAlgebra
  have hSH : SH R (FractionRing R) := by
    show _ ∧ _ ∧ _ ∧ _
    exact ⟨inferInstance, hhen, hac, inferInstance⟩
  have hmodR : IsModel (L := FractionRing R) B ((Over.pullback (spMap (algebraMap W R))).obj G) :=
    isModel_pullback (algebraMap W R) b hbW rfl B G hmod
  have hsemiR : IsSemiAbelian ((Over.pullback (spMap (algebraMap W R))).obj G) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (spMap (algebraMap W R)) G hG'
  obtain ⟨GR, _, hsc, hmodA, ht⟩ := exists_model_of_isogeny K R (FractionRing R) hSH A B g m hA hP hgA hgB
    i r hm hri _ hsemiR hmodR
  letI : Algebra V R := ((algebraMap W R).comp (algebraMap V W)).toAlgebra
  have hVR : (algebraMap R (FractionRing R)).comp (algebraMap V R) =
      (algebraMap K (FractionRing R)).comp (algebraMap V K) := by
    change (algebraMap R (FractionRing R)).comp ((algebraMap W R).comp (algebraMap V W)) =
      (b.comp (algebraMap K L)).comp (algebraMap V K)
    rw [← RingHom.comp_assoc, hbW, RingHom.comp_assoc, hc, RingHom.comp_assoc]
  obtain ⟨s, hs⟩ := GlobalTheory.smConn_model_descends V K R (FractionRing R) hVR A hA GR hsc hmodA
  have hVW : Function.Injective (algebraMap V W) := by
    have h2 : Function.Injective ((algebraMap K L).comp (algebraMap V K)) :=
      (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    rw [← hc, RingHom.coe_comp] at h2
    exact h2.of_comp
  haveI : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have hVRi : (algebraMap V R).IsIntegral :=
    RingHom.IsIntegral.trans (f := algebraMap V W) (g := algebraMap W R)
      (fun x => Algebra.IsIntegral.isIntegral (R := V) x) (fun x => hint.isIntegral x)
  have hVRinj : Function.Injective (algebraMap V R) := hinj.comp hVW
  obtain ⟨hlocVR, -, hdescV⟩ := GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr V R hVRinj ⟨fun x => hVRi x⟩
  obtain ⟨W', _, hsW, hcW, hfW, hlW⟩ := hdescV s
  obtain ⟨GW, _, _, ε, hscW, hε, hcompW, hmodW⟩ := hs W' inferInstance hsW hlW
  haveI := hε
  have hlVW : IsLocalHom (algebraMap V W') := by
    refine ⟨fun x hx => ?_⟩
    have h1 : IsUnit (W'.val.toRingHom (algebraMap V W' x)) := hx.map _
    exact IsLocalHom.map_nonunit (f := algebraMap V R) x h1
  let ρ : W' →+* ResidueField R := (residue R).comp W'.val.toRingHom
  have hker : RingHom.ker ρ = maximalIdeal W' := by
    rw [← RingHom.comap_ker, ker_residue, maximalIdeal_comap]
  have hρi : ρ.IsIntegral :=
    RingHom.IsIntegral.trans (f := W'.val.toRingHom) (g := residue R)
      (RingHom.IsIntegral.tower_top (f := algebraMap V W') (g := W'.val.toRingHom) hVRi)
      (RingHom.isIntegral_of_surjective _ residue_surjective)
  have htor : Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj GW)) := by
    obtain ⟨T⟩ := ht
    have hρ : spMap ρ = spMap (residue R) ≫ spMap W'.val.toRingHom := (Isog.spMap_comp _ _).symm
    rw [hρ]
    let Z := pullCompIso (spMap (residue R)) (spMap W'.val.toRingHom) GW ≪≫ (Over.pullback _).mapIso ε
    haveI : IsMonHom Z.symm.hom := by
      dsimp only [Z, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv]
      infer_instance
    exact ⟨torusExtOfIso Z.symm T⟩
  have hprop : IsProper ((Over.pullback (spMap (algebraMap W' (FractionRing W')))).obj GW).hom := by
    obtain ⟨e, -⟩ := hmodW
    haveI : IsProper A.hom := hA.proper
    haveI : IsProper ((Over.pullback (spMap (algebraMap K (FractionRing W')))).obj A).hom :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap K (FractionRing W')))) (inferInstanceAs (IsProper A.hom))
    haveI : IsIso e.hom.left := ⟨e.inv.left, by simp [← Over.comp_left], by simp [← Over.comp_left]⟩
    rw [← Over.w e.hom]
    infer_instance
  have hsemiW : IsSemiAbelian GW :=
    isSemiAbelian_of_proper_generic_of_torusExtension W' (FractionRing W') GW hscW hprop
      (ResidueField R) ρ hker hρi htor
  unfold PotModel
  exact ⟨W', FractionRing W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcompW, hfW, hlVW, hcW, GW, inferInstance, hmodW, hsemiW⟩

end GlobalTheory.SS
