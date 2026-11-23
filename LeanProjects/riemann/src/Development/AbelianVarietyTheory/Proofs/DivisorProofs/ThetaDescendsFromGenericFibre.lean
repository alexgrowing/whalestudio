import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaExtend

theorem isRegularRing_sections {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsRegularRing Γ(Y, V) := by
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  rw [isRegularRing_iff]
  intro q hq
  let y : PrimeSpectrum Γ(Y, V) := ⟨q, hq⟩
  have hy : hV.fromSpec y ∈ V := hV.range_fromSpec.le ⟨y, rfl⟩
  let : Algebra Γ(Y, V) (Y.presheaf.stalk (hV.fromSpec y)) :=
    Y.presheaf.algebra_section_stalk ⟨hV.fromSpec y, hy⟩
  have h : IsLocalization q.primeCompl (Y.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hy
  have := hY (hV.fromSpec y)
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Y.presheaf.stalk (hV.fromSpec y))
      (Localization.AtPrime q)).toRingEquiv

theorem isRegularRing_stalk {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) (f : X ⟶ Y) [Smooth f] (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).isOpen
  have hs : (f.appLE V U hUV).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have := isRegularRing_sections hY hV
  algebraize [(f.appLE V U hUV).hom]
  have : IsRegularRing Γ(X, U) := isRegularRing_of_smooth Γ(Y, V) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact ExtendRig.isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

theorem ufd_of_regular (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE R

theorem hasTheta_of_generic {Y : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) (P : PPAS Y) (Q : PPAS (Sp Y.functionField))
    (ψ : Q.A.left ⟶ P.A.left) (hQ : Q.IsPull P (Y.fromSpecStalk (genericPoint Y)) ψ)
    (hT : Q.HasTheta) : P.HasTheta := by
  obtain ⟨h, hc⟩ := hQ
  obtain ⟨L₀, hL₀, hs, hp⟩ := hT
  let j : Sp Y.functionField ⟶ Y := Y.fromSpecStalk (genericPoint Y)
  have hj₁ : IsPreimmersion j := inferInstanceAs (IsPreimmersion (Y.fromSpecStalk _))
  have hj₂ : Flat j := GenericExt.flat_fromSpecStalk Y _
  have hj₃ : IsDominant j := ⟨by
    refine Dense.mono (s₁ := {genericPoint Y}) ?_ (dense_iff_closure_eq.2 (genericPoint_spec Y))
    rintro _ rfl
    exact ⟨_, Scheme.fromSpecStalk_closedPoint⟩⟩
  have hj₄ : QuasiCompact j := inferInstance
  have hn : Geo.Tor.IsNormalScheme Y := fun y => by
    have := isRegularRing_stalk hY (𝟙 Y) y
    have := ufd_of_regular (Y.presheaf.stalk y)
    exact ⟨inferInstance, inferInstance⟩
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian P.A.hom
  have : IsLocallyNoetherian P.A.left := LocallyOfFiniteType.isLocallyNoetherian P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have := Q.isAb.smooth
  have := Q.isAb.geomConnected
  have : GeometricallyIntegral Q.A.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral Q.A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian Q.A.hom
  have : IsPreimmersion ψ := MorphismProperty.of_isPullback (P := @IsPreimmersion) h.1.flip hj₁
  have : Flat ψ := MorphismProperty.of_isPullback (P := @Flat) h.1.flip hj₂
  obtain ⟨L, hL, hLL⟩ := exists_lineBundle_extension_of_generalizing P.A.left Q.A.left ψ
    (Flat.generalizingMap ψ) (fun x => have := isRegularRing_stalk hY P.A.hom x; ufd_of_regular _) L₀ hL₀
  have e₀ : pull ψ (cls L hL) = cls L₀ hL₀ := (cls_eq_iff (pull_isLB hL ψ) hL₀).2 hLL
  let κ : ∀ {T : Over Y}, (T ⟶ P.A) → (pullback T.hom j ⟶ Q.A.left) := fun {T} a =>
    h.1.lift (pullback.fst _ _ ≫ a.left) (pullback.snd _ _) (by
      rw [Category.assoc, Over.w]; exact pullback.condition)
  have κ₁ : ∀ {T : Over Y} (a : T ⟶ P.A), κ a ≫ ψ = pullback.fst _ _ ≫ a.left := fun a =>
    h.1.lift_fst _ _ _
  have κ₂ : ∀ {T : Over Y} (a : T ⟶ P.A), κ a ≫ Q.A.hom = pullback.snd _ _ := fun a =>
    h.1.lift_snd _ _ _
  refine ⟨L, hL, OddDescent.sym_of_pull_inv_cls P.A hL ?_, ?_⟩
  · refine ZH.EndoExtend.pic_ext j hn P.A (eSec P.A) (Over.w η[P.A]) ?_ ?_
    · rw [← pull_comp, OddDescent.eSec_inv]
    · have e : pullback.fst P.A.hom j = κ (𝟙 _) ≫ ψ := ((κ₁ _).trans (Category.comp_id _)).symm
      rw [e, pull_comp, pull_comp, ← pull_comp ψ, ← OddDescent.inv_left_comp h, pull_comp, e₀,
        OddDescent.pull_inv_cls_of_sym Q.A hL₀ hs]
  · have := smooth_tensorObj_hom P.A P.A
    have := geometricallyIntegral_tensorObj_hom P.A P.A
    refine ZH.EndoExtend.pic_ext j hn (P.A ⊗ P.A) (η[P.A] ≫ lift (1 : P.A ⟶ P.A) (𝟙 P.A)).left
      (Over.w _) ?_ ?_
    · rw [Over.comp_left, pull_comp, pull_comp, P.isPol.1, pull_lam, lift_fst, lam_one_left]
    · let δ : pullback (P.A ⊗ P.A).hom j ⟶ (Q.A ⊗ Q.A).left :=
        pullback.lift (κ (fst _ _)) (κ (snd _ _)) ((κ₂ _).trans (κ₂ _).symm)
      have e : pullback.fst (P.A ⊗ P.A).hom j = δ ≫ sqMap h.1.w := by
        apply pullback.hom_ext
        · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_fst, δ, pullback.lift_fst_assoc]
          exact (κ₁ (fst P.A P.A)).symm
        · simp only [sqMap, pullback.map, Category.assoc, pullback.lift_snd, δ, pullback.lift_snd_assoc]
          exact (κ₁ (snd P.A P.A)).symm
      rw [e, pull_comp, pull_comp, ← hc, hp, PPAS.pull_sqMap_lam h, e₀]

theorem hasTheta_of_regSurf : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsRegSurf q → ∀ P : PPAS Y, (∃ (Q : PPAS (Sp Y.functionField)) (ψ : Q.A.left ⟶ P.A.left), Q.IsPull P (Y.fromSpecStalk (genericPoint Y)) ψ ∧ Q.HasTheta) → P.HasTheta := by
  rintro k _ Y _ q hq P ⟨Q, ψ, hQ, hT⟩
  have := hq.toIsArithVar.isNoetherian
  exact hasTheta_of_generic hq.regular P Q ψ hQ hT

end GlobalTheory.ThetaExtend
