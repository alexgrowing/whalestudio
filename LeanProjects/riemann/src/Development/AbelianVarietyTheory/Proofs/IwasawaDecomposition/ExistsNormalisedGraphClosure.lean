import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GraphClosure

theorem charZero_residueField_of_flat {R : Type} [CommRing R] [IsDomain R] [CharZero R] {W : Scheme.{0}}
    (s : W ⟶ Sp R) [Flat s] {x : W} (hx : x ∈ genericPoints W) : CharZero (W.residueField x) := by
  have hsp : genericPoint (Sp R) ⤳ s x := (genericPoint_spec (Sp R)).specializes trivial
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap s hsp
  obtain rfl := eq_of_specializes_of_mem_genericPoints hx hx'
  have : CharZero ((Sp R).residueField (s x')) := by
    rw [e]
    have : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨genericPoint (Sp R), trivial⟩⟩
    have : CharZero (Sp R).functionField :=
      charZero_of_injective_ringHom (R := R)
        (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom)
        (((Sp R).germToFunctionField_injective ⊤).comp
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)
    exact charZero_of_injective_ringHom (R := (Sp R).functionField)
      ((Sp R).residue (genericPoint (Sp R))).hom.injective
  exact charZero_of_injective_ringHom (s.residueFieldMap x').hom.injective

theorem exists_normalised_graph_closure : ∀ (O O₂ : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [CommRing O₂] (b : O₂ →+* O) (X₁ X₂ : Scheme.{0}) (s₁ : X₁ ⟶ Sp O) (s₂ : X₂ ⟶ Sp O₂) (U : X₁.Opens) (g : U.toScheme ⟶ X₂), IsProjOver s₁ → IsProjOver s₂ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X₁ → Flat s₁ → g ≫ s₂ = U.ι ≫ s₁ ≫ spMap b → ∃ (X' : Scheme.{0}) (f₁ : X' ⟶ X₁) (f₂ : X' ⟶ X₂) (j : U.toScheme ⟶ X'), IsProjOver (f₁ ≫ s₁) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Flat (f₁ ≫ s₁) ∧ IsPullback j (𝟙 U.toScheme) f₁ U.ι ∧ Dense (Set.range j) ∧ j ≫ f₂ = g ∧ IsFinite (prod.lift f₁ f₂) := by
  intro O O₂ _ _ _ _ b X₁ X₂ s₁ s₂ U g h₁ h₂ hn _ w
  have : IsProper s₁ := ((isProjOver_iff_isProper_and_exists_isAmpleLB s₁).mp h₁).1
  have : IsProper s₂ := ((isProjOver_iff_isProper_and_exists_isAmpleLB s₂).mp h₂).1
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian s₁
  obtain ⟨P, p₁, p₂, H, hP⟩ : ∃ (P : Scheme.{0}) (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂),
      IsPullback p₁ p₂ (s₁ ≫ spMap b) s₂ ∧ IsProjOver (p₁ ≫ s₁) :=
    ⟨_, _, _, ((IsPullback.of_hasPullback s₁ (pullback.snd s₂ (spMap b))).paste_vert
      (IsPullback.of_hasPullback s₂ (spMap b)).flip),
      ProjSpace.isProjOver_pullback h₁ (ProjSpace.isProjOver_pullback_snd b h₂)⟩
  have : IsProper p₁ := MorphismProperty.of_isPullback H.flip ‹IsProper s₂›
  let h : U.toScheme ⟶ P := H.lift U.ι g w.symm
  have e₁ : h ≫ p₁ = U.ι := H.lift_fst _ _ _
  have e₂ : h ≫ p₂ = g := H.lift_snd _ _ _
  have : QuasiCompact (h ≫ p₁) := e₁ ▸ inferInstance
  have : QuasiCompact h := .of_comp h p₁
  have : IsSeparated (h ≫ p₁) := e₁ ▸ inferInstance
  have : IsSeparated h := .of_comp h p₁
  have : LocallyOfFiniteType (h ≫ p₁) := e₁ ▸ inferInstance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h p₁
  have : IsFinite h.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of O) h (p₁ ≫ s₁)
      fun x hx => charZero_residueField_of_flat (U.ι ≫ s₁) hx
  have : Flat (h.toNormalization ≫ (h.fromNormalization ≫ p₁) ≫ s₁) := by
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc, reassoc_of% e₁]
    infer_instance
  let c : U.toScheme ⟶ pullback p₁ U.ι := pullback.lift h (𝟙 _) (by simpa using e₁)
  have hc₁ : c ≫ pullback.fst _ _ = h := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.snd _ _) := by rw [hc₂]; infer_instance
  have : IsClosedImmersion c := .of_comp c (pullback.snd _ _)
  have Q := (isPullback_toNormalization_of_mono c (pullback.fst p₁ U.ι) h hc₁.symm).paste_vert
    (IsPullback.of_hasPullback p₁ U.ι)
  rw [hc₂] at Q
  have : IsSeparated (terminal.from X₂) := by
    rw [← terminal.comp_from s₂]; infer_instance
  have : IsSeparated (prod.fst : X₁ ⨯ X₂ ⟶ X₁) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasBinaryProduct' X₁ X₂).flip this
  have : IsProper (prod.lift p₁ p₂ ≫ prod.fst) := by rwa [prod.lift_fst]
  have : IsProper (prod.lift p₁ p₂) := .of_comp _ prod.fst
  have : Mono (prod.lift p₁ p₂) := ⟨fun u v e => H.hom_ext
    (by simpa only [Category.assoc, prod.lift_fst] using congrArg (· ≫ prod.fst) e)
    (by simpa only [Category.assoc, prod.lift_snd] using congrArg (· ≫ prod.snd) e)⟩
  have : IsClosedImmersion (prod.lift p₁ p₂) :=
    (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨inferInstance, inferInstance⟩
  refine ⟨h.normalization, h.fromNormalization ≫ p₁, h.fromNormalization ≫ p₂, h.toNormalization, ?_,
    IsNormalScheme.pred _, flat_normalization h _, Q, h.toNormalization.denseRange, by simp [e₂], ?_⟩
  · rw [Category.assoc]
    exact isProjOver_comp_of_isFinite _ hP
  · rw [← prod.comp_lift]
    infer_instance

end GlobalTheory.GraphClosure
