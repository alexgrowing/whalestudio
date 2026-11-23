import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IotaCompTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubringStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableExtensionMultiplesOfSemistable
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbHomDesc

theorem exists_baseChange_subring : ∀ (R : Type) [CommRing R] (S S' : Subring R) (h : S ≤ S') (g : ℕ) (A : Over (Sp R)) [GrpObj A] (AS : Over (Sp S)) [GrpObj AS] (φ : A.left ⟶ AS.left), IsAbelianScheme AS → SmoothOfRelativeDimension g AS.hom → IsGrpPullback A AS (spMap S.subtype) φ → ∃ (AS' : Over (Sp S')) (_ : GrpObj AS') (φ' : A.left ⟶ AS'.left) (ρ : AS'.left ⟶ AS.left), IsAbelianScheme AS' ∧ SmoothOfRelativeDimension g AS'.hom ∧ IsGrpPullback A AS' (spMap S'.subtype) φ' ∧ IsGrpPullback AS' AS (spMap (Subring.inclusion h)) ρ ∧ φ' ≫ ρ = φ := by
  intro R _ S S' h g A _ AS _ φ hab hsm hφ
  have e : spMap S.subtype = spMap S'.subtype ≫ spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  have hf := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (spMap (Subring.inclusion h)) (spMap S'.subtype)
    (hφ.congr e rfl)
  have hs : SmoothOfRelativeDimension g ((Over.pullback (spMap (Subring.inclusion h))).obj AS).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hsm
  exact ⟨_, inferInstance, _, pullback.fst _ _, isAbelianScheme_overPullback _ AS hab, hs, hf,
    isGrpPullback_pullback _ _, pullback.lift_fst _ _ _⟩

theorem exists_finset_le_of_finiteType : ∀ (R : Type) [CommRing R] (S : Subring R), Algebra.FiniteType ℤ S → ∃ F : Finset R, ∀ T : Subring R, (F : Set R) ⊆ T → S ≤ T := by
  intro R _ S hS
  classical
  obtain ⟨s, hs⟩ := hS.out
  refine ⟨s.image Subtype.val, fun T hT x hx => ?_⟩
  suffices key : ∀ y : S, y ∈ Algebra.adjoin ℤ (s : Set S) → (y : R) ∈ T from
    key ⟨x, hx⟩ (hs ▸ Algebra.mem_top)
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact hT (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hy))
  | algebraMap n =>
    rw [eq_intCast]
    push_cast
    exact intCast_mem T n
  | add y z _ _ hy hz => exact T.add_mem hy hz
  | mul y z _ _ hy hz => exact T.mul_mem hy hz

theorem exists_isPullback_reductions : ∀ (R : Type) [CommRing R] (I : Ideal R) (S S' : Subring R) (h : S ≤ S') (AS : Over (Sp S)) (AS' : Over (Sp S')) (ρ : AS'.left ⟶ AS.left), IsPullback ρ AS'.hom AS.hom (spMap (Subring.inclusion h)) → ∃ p : pullback AS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype))) ⟶ pullback AS.hom (spMap (Ideal.Quotient.mk (I.comap S.subtype))), IsPullback p (pullback.snd _ _) (pullback.snd _ _) (spMap (GlobalTheory.AbHomDesc.trans I h)) ∧ p ≫ pullback.fst _ _ = pullback.fst _ _ ≫ ρ := by
  intro R _ I S S' h AS AS' ρ hρ
  have e : spMap (Ideal.Quotient.mk (I.comap S'.subtype)) ≫ spMap (Subring.inclusion h) =
      spMap (trans I h) ≫ spMap (Ideal.Quotient.mk (I.comap S.subtype)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, trans_comp_mk]
  have big := (IsPullback.of_hasPullback AS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).paste_horiz hρ
  rw [e] at big
  refine ⟨pullback.lift (pullback.fst _ _ ≫ ρ) (pullback.snd _ _ ≫ spMap (trans I h))
    (by simp only [Category.assoc]; rw [hρ.w, pullback.condition_assoc, e]), ?_, pullback.lift_fst _ _ _⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rwa [pullback.lift_fst]

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (f : B →+* C) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isIso_spMap {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B) : IsIso (spMap (f : A →+* B)) := by
  have : IsIso (CommRingCat.ofHom (f : A →+* B)) := f.toCommRingCatIso.isIso_hom
  infer_instance

noncomputable def redEquiv {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) : S ⧸ I.comap S.subtype ≃+* (iota I π hI S).range :=
  RingEquiv.ofBijective (iota I π hI S).rangeRestrict
    ⟨fun x y hxy => iota_injective I π hI S (congrArg Subtype.val hxy), (iota I π hI S).rangeRestrict_surjective⟩

theorem iota_redEquiv_symm {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp ((redEquiv I π hI S).symm : _ →+* _) = (iota I π hI S).range.subtype := by
  ext t
  exact congrArg Subtype.val ((redEquiv I π hI S).apply_symm_apply t)

noncomputable def redInv {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) : (iota I π hI S).range →+* S ⧸ I.comap S.subtype :=
  (redEquiv I π hI S).symm.toRingHom

instance isIso_spMap_redInv {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) : IsIso (spMap (redInv I π hI S)) :=
  isIso_spMap (redEquiv I π hI S).symm

theorem iota_redInv {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hI : RingHom.ker π = I) (S : Subring R) :
    (iota I π hI S).comp (redInv I π hI S) = (iota I π hI S).range.subtype :=
  iota_redEquiv_symm I π hI S

theorem morphism_descends_to_reduction : ∀ (R : Type) [CommRing R] (I : Ideal R) (R₀ : Type) [CommRing R₀] (π : R →+* R₀) (hπ : Function.Surjective π) (hI : RingHom.ker π = I) (S : Subring R) (X X₀ Y₀ : Scheme.{0}) (p : X ⟶ Sp R₀) (a : X₀ ⟶ Sp (S ⧸ I.comap S.subtype)) (b : Y₀ ⟶ Sp (S ⧸ I.comap S.subtype)) (π' : X ⟶ X₀) [QuasiCompact a] [QuasiSeparated a] [LocallyOfFinitePresentation b] (φ : X ⟶ Y₀), IsPullback π' p a (spMap (GlobalTheory.AbHomDesc.iota I π hI S)) → φ ≫ b = π' ≫ a → ∃ F : Finset R, ∀ (S' : Subring R) (h : S ≤ S'), (F : Set R) ⊆ S' → ∀ (X₁ : Scheme.{0}) (a₁ : X₁ ⟶ Sp (S' ⧸ I.comap S'.subtype)) (π₁ : X₁ ⟶ X₀) (k : X ⟶ X₁), IsPullback π₁ a₁ a (spMap (GlobalTheory.AbHomDesc.trans I h)) → k ≫ π₁ = π' → k ≫ a₁ = p ≫ spMap (GlobalTheory.AbHomDesc.iota I π hI S') → ∃ ψ : X₁ ⟶ Y₀, k ≫ ψ = φ ∧ ψ ≫ b = π₁ ≫ a := by
  intro R _ I R₀ _ π hπ hI S X X₀ Y₀ p a b π' _ _ _ φ hpb hφ
  classical
  have hpb' : IsPullback π' p (a ≫ spMap (redInv I π hI S)) (spMap (iota I π hI S).range.subtype) := by
    refine IsPullback.of_iso hpb (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (spMap (redInv I π hI S))) (by simp) (by simp) (by simp) ?_
    rw [Iso.refl_hom, Category.id_comp, asIso_hom, spMap_comp_spMap, iota_redInv]
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.morphism_descends_to_subring R₀ (iota I π hI S).range X X₀ Y₀ p
    (a ≫ spMap (redInv I π hI S)) (b ≫ spMap (redInv I π hI S)) π' φ hpb'
    (by rw [← Category.assoc, hφ, Category.assoc])
  refine ⟨F₀.image (Function.surjInv hπ), fun S' h hF X₁ a₁ π₁ k hpb₁ hk₁ hk₂ => ?_⟩
  have hT : (iota I π hI S).range ≤ (iota I π hI S').range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨trans I h x, by rw [← RingHom.comp_apply, iota_comp_trans]⟩
  have hFT : (F₀ : Set R₀) ⊆ (iota I π hI S').range := by
    intro y hy
    have hm : Function.surjInv hπ y ∈ S' := hF (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hy))
    exact ⟨Ideal.Quotient.mk _ ⟨_, hm⟩, Function.surjInv_eq hπ y⟩
  have hring : (trans I h).comp (redInv I π hI S) = (redInv I π hI S').comp (Subring.inclusion hT) := by
    ext t
    apply (redEquiv I π hI S').injective
    show redEquiv I π hI S' (trans I h (redInv I π hI S t)) =
      redEquiv I π hI S' ((redEquiv I π hI S').symm (Subring.inclusion hT t))
    rw [RingEquiv.apply_symm_apply]
    apply Subtype.ext
    show iota I π hI S' (trans I h (redInv I π hI S t)) = (t : R₀)
    rw [← RingHom.comp_apply, iota_comp_trans, ← RingHom.comp_apply, iota_redInv]
    rfl
  have hpb₁' : IsPullback π₁ (a₁ ≫ spMap (redInv I π hI S')) (a ≫ spMap (redInv I π hI S))
      (spMap (Subring.inclusion hT)) := by
    refine IsPullback.of_iso hpb₁ (Iso.refl _) (Iso.refl _) (asIso (spMap (redInv I π hI S')))
      (asIso (spMap (redInv I π hI S))) (by simp) (by simp) (by simp) ?_
    rw [asIso_hom, asIso_hom, spMap_comp_spMap, spMap_comp_spMap, hring]
  have hk₂' : k ≫ a₁ ≫ spMap (redInv I π hI S') = p ≫ spMap (iota I π hI S').range.subtype := by
    rw [← Category.assoc, hk₂, Category.assoc, spMap_comp_spMap, iota_redInv]
  obtain ⟨ψ, hψ₁, hψ₂⟩ := hF₀ _ hT hFT X₁ _ π₁ k hpb₁' hk₁ hk₂'
  refine ⟨ψ, hψ₁, ?_⟩
  rw [← Category.assoc, ← Category.assoc] at hψ₂
  exact (cancel_mono _).1 hψ₂

theorem exists_isGrpPullback_reduction : ∀ (R : Type) [CommRing R] (I : Ideal R) (R₀ : Type) [CommRing R₀] (π : R →+* R₀) (hI : RingHom.ker π = I) (S : Subring R) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left) (AS : Over (Sp S)) [GrpObj AS] (φ : A.left ⟶ AS.left), IsGrpPullback A₀ A (spMap π) i → IsGrpPullback A AS (spMap S.subtype) φ → ∃ ψ : A₀.left ⟶ ((Over.pullback (spMap (Ideal.Quotient.mk (I.comap S.subtype)))).obj AS).left, IsGrpPullback A₀ ((Over.pullback (spMap (Ideal.Quotient.mk (I.comap S.subtype)))).obj AS) (spMap (GlobalTheory.AbHomDesc.iota I π hI S)) ψ ∧ i ≫ φ = ψ ≫ pullback.fst AS.hom (spMap (Ideal.Quotient.mk (I.comap S.subtype))) := by
  intro R _ I R₀ _ π hI S A₀ _ A _ i AS _ φ hA hφ
  have e : spMap π ≫ spMap S.subtype =
      spMap (iota I π hI S) ≫ spMap (Ideal.Quotient.mk (I.comap S.subtype)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, iota_comp_mk]
  have h := (hA.comp hφ).congr e rfl
  exact ⟨_, ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor _ _ h, (pullback.lift_fst _ _ _).symm⟩

theorem abelian_hom_reduction_descends : ∀ (R : Type) [CommRing R] (I : Ideal R) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
    IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left),
    IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀],
  ∃ (S : Subring R) (ι₀ : (S ⧸ I.comap S.subtype) →+* R₀)
    (AS₀ : Over (Sp (S ⧸ I.comap S.subtype))) (_ : GrpObj AS₀) (AS : Over (Sp S)) (_ : GrpObj AS) (iS : AS₀.left ⟶ AS.left)
    (BS₀ : Over (Sp (S ⧸ I.comap S.subtype))) (_ : GrpObj BS₀) (BS : Over (Sp S)) (_ : GrpObj BS) (jS : BS₀.left ⟶ BS.left)
    (fS₀ : AS₀ ⟶ BS₀) (φA : A.left ⟶ AS.left) (φB : B.left ⟶ BS.left) (ψA : A₀.left ⟶ AS₀.left) (ψB : B₀.left ⟶ BS₀.left),
    Algebra.FiniteType ℤ S ∧ ι₀.comp (Ideal.Quotient.mk (I.comap S.subtype)) = π.comp S.subtype ∧ IsMonHom fS₀ ∧
    IsGrpPullback AS₀ AS (spMap (Ideal.Quotient.mk (I.comap S.subtype))) iS ∧
    IsGrpPullback BS₀ BS (spMap (Ideal.Quotient.mk (I.comap S.subtype))) jS ∧
    IsAbelianScheme AS ∧ SmoothOfRelativeDimension g AS.hom ∧ IsAbelianScheme BS ∧ SmoothOfRelativeDimension g' BS.hom ∧
    IsGrpPullback A AS (spMap S.subtype) φA ∧ IsGrpPullback B BS (spMap S.subtype) φB ∧
    IsGrpPullback A₀ AS₀ (spMap ι₀) ψA ∧ IsGrpPullback B₀ BS₀ (spMap ι₀) ψB ∧
    i ≫ φA = ψA ≫ iS ∧ j ≫ φB = ψB ≫ jS ∧ f₀.left ≫ ψB = ψA ≫ fS₀.left := by
  intro R _ I R₀ _ π hπ hI g A₀ _ A _ i hA hAab hAsm g' B₀ _ B _ j hB hBab hBsm f₀ _

  obtain ⟨S₀, AS₀, _, φA₀, -, hfg₀, hAS₀ab, hAS₀sm, hφA₀⟩ := GlobalTheory.T.abelianScheme_descends_to_finitelyGenerated_subring R g A ∅ hAab hAsm
  obtain ⟨F₀, hF₀⟩ := exists_finset_le_of_finiteType R S₀ hfg₀
  obtain ⟨S₁, BS₁, _, φB₁, hF₀S₁, hfg₁, hBS₁ab, hBS₁sm, hφB₁⟩ := GlobalTheory.T.abelianScheme_descends_to_finitelyGenerated_subring R g' B F₀ hBab hBsm
  obtain ⟨AS₁, _, φA₁, -, hAS₁ab, hAS₁sm, hφA₁, -, -⟩ :=
    exists_baseChange_subring R S₀ S₁ (hF₀ S₁ hF₀S₁) g A AS₀ φA₀ hAS₀ab hAS₀sm hφA₀

  obtain ⟨ψA, hψA, hiA⟩ := exists_isGrpPullback_reduction R I R₀ π hI S₁ A₀ A i AS₁ φA₁ hA hφA₁
  obtain ⟨ψB, hψB, hiB⟩ := exists_isGrpPullback_reduction R I R₀ π hI S₁ B₀ B j BS₁ φB₁ hB hφB₁
  have wA : ψA ≫ pullback.snd AS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))) =
      A₀.hom ≫ spMap (iota I π hI S₁) := hψA.1.w
  have wB : ψB ≫ pullback.snd BS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))) =
      B₀.hom ≫ spMap (iota I π hI S₁) := hψB.1.w

  have := hAS₁ab.proper
  have := hBS₁ab.smooth
  have hw : (f₀.left ≫ ψB) ≫ pullback.snd BS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))) =
      ψA ≫ pullback.snd AS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))) := by
    rw [Category.assoc, wB, wA, ← Category.assoc, Over.w f₀]
  obtain ⟨F, hF⟩ := morphism_descends_to_reduction R I R₀ π hπ hI S₁ A₀.left _ _ A₀.hom
    (pullback.snd AS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype))))
    (pullback.snd BS₁.hom (spMap (Ideal.Quotient.mk (I.comap S₁.subtype)))) ψA (f₀.left ≫ ψB) hψA.1 hw

  obtain ⟨S', h, hFS, hfg'⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S₁ F hfg₁
  obtain ⟨AS', _, φA', ρA, hAS'ab, hAS'sm, hφA', hρA, hφρA⟩ := exists_baseChange_subring R S₁ S' h g A AS₁ φA₁ hAS₁ab hAS₁sm hφA₁
  obtain ⟨BS', _, φB', ρB, hBS'ab, hBS'sm, hφB', hρB, hφρB⟩ := exists_baseChange_subring R S₁ S' h g' B BS₁ φB₁ hBS₁ab hBS₁sm hφB₁
  obtain ⟨ψA', hψA', hiA'⟩ := exists_isGrpPullback_reduction R I R₀ π hI S' A₀ A i AS' φA' hA hφA'
  obtain ⟨ψB', hψB', hiB'⟩ := exists_isGrpPullback_reduction R I R₀ π hI S' B₀ B j BS' φB' hB hφB'
  have wA' : ψA' ≫ pullback.snd AS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype))) =
      A₀.hom ≫ spMap (iota I π hI S') := hψA'.1.w
  have wB' : ψB' ≫ pullback.snd BS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype))) =
      B₀.hom ≫ spMap (iota I π hI S') := hψB'.1.w
  obtain ⟨pA, hpA, hpAf⟩ := exists_isPullback_reductions R I S₁ S' h AS₁ AS' ρA hρA.1
  obtain ⟨pB, hpB, hpBf⟩ := exists_isPullback_reductions R I S₁ S' h BS₁ BS' ρB hρB.1
  have eι : spMap (iota I π hI S') ≫ spMap (trans I h) = spMap (iota I π hI S₁) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, iota_comp_trans]
  have cA : ψA' ≫ pA = ψA := by
    apply pullback.hom_ext
    · rw [Category.assoc, hpAf, ← Category.assoc, ← hiA', Category.assoc, hφρA, hiA]
    · rw [Category.assoc, hpA.w, ← Category.assoc, wA', Category.assoc, eι, wA]
  have cB : ψB' ≫ pB = ψB := by
    apply pullback.hom_ext
    · rw [Category.assoc, hpBf, ← Category.assoc, ← hiB', Category.assoc, hφρB, hiB]
    · rw [Category.assoc, hpB.w, ← Category.assoc, wB', Category.assoc, eι, wB]
  obtain ⟨ψ, hψ₁, hψ₂⟩ := hF S' h hFS _ (pullback.snd AS'.hom _) pA ψA' hpA cA wA'
  let fl := hpB.lift ψ (pullback.snd AS'.hom (spMap (Ideal.Quotient.mk (I.comap S'.subtype))))
    (by rw [hψ₂, hpA.w])
  let fS : (Over.pullback (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).obj AS' ⟶
      (Over.pullback (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).obj BS' :=
    Over.homMk fl (hpB.lift_snd _ _ _)
  have key : f₀.left ≫ ψB' = ψA' ≫ fS.left := by
    apply hpB.hom_ext
    · rw [Category.assoc, cB]
      show _ = ψA' ≫ fl ≫ pB
      rw [hpB.lift_fst, hψ₁]
    · rw [Category.assoc, wB', ← Category.assoc, Over.w f₀]
      show _ = ψA' ≫ fl ≫ _
      rw [hpB.lift_snd, wA']

  have : IsSchemeTheoreticallyDominant (spMap (iota I π hI S')) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ (iota_injective I π hI S')
  have := hAS'ab.smooth
  have := hBS'ab.proper
  have : Flat ((Over.pullback (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).obj AS').hom := by
    show Flat (pullback.snd _ _); infer_instance
  have : IsSeparated ((Over.pullback (spMap (Ideal.Quotient.mk (I.comap S'.subtype)))).obj BS').hom := by
    show IsSeparated (pullback.snd _ _); infer_instance
  have hmon : IsMonHom fS := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback hψA' hψB' f₀ fS key
  exact ⟨S', iota I π hI S', _, inferInstance, AS', inferInstance, pullback.fst _ _, _, inferInstance, BS',
    inferInstance, pullback.fst _ _, fS, φA', φB', ψA', ψB', hfg', iota_comp_mk I π hI S', hmon,
    isGrpPullback_pullback _ _, isGrpPullback_pullback _ _, hAS'ab, hAS'sm, hBS'ab, hBS'sm, hφA', hφB', hψA',
    hψB', hiA', hiB', key⟩

end GlobalTheory.AbHomDesc
