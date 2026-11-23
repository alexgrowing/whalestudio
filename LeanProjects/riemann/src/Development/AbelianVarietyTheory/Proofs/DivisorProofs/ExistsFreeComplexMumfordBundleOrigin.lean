import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexPrimitiveLineBundleCechFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingPointsIdealCriterionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.MumfordLocalComplex
open GlobalTheory.CechPic GlobalTheory.StabFlat GlobalTheory.PrimitiveOverValuationRing

theorem exists_ideal_complex_cech (hG : GlobalFnsSt) {V : Type} [CommRing V] (B : Over (Spec (CommRingCat.of V)))
    [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ}
    (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a) :
    ∃ (I : Ideal A) (C : CochainComplex (ModuleCat.{0} A) ℕ), (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧
      (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧
      Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] A ⧸ I) ∧
      (∀ p : Ideal A, p.IsPrime → ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p ∧
        ∀ i, (¬ I ≤ p ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧
      (∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
        (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
          I ≤ RingHom.ker φ) ∧
      ∀ (K : Type) [Field K] (φ : A →+* K),
        (∃ y : Spec (CommRingCat.of K) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) →
        ∀ (X' : Scheme.{0}) (π' : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)),
        IsPullback π' f' B.hom (Spec.map (CommRingCat.ofHom φ) ≫ a ≫ B.hom) →
        ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X'.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
        ∀ i, Nonempty ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i ≃ₗ[K]
          (cechLB f' (LB.triv X') D).homology i) := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃, c₄⟩ := GlobalTheory.T.exists_free_complex_primitive_lineBundle_cech_fibres A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, C, c₁, c₂, ⟨eC.trans eI⟩, fun p _ => ?_, fun R _ _ φ =>
    (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans (hI R φ _ _ _ (IsPullback.of_hasPullback _ _)), ?_⟩
  · let K := AlgebraicClosure p.ResidueField
    let φ : A →+* K := (algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)
    have hk : RingHom.ker φ = p := by
      rw [RingHom.ker_comp_of_injective _ (algebraMap p.ResidueField K).injective, Ideal.ker_algebraMap_residueField]
    refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
    rcases hi with hi | hi
    · exact Or.inr fun ht => hi (hk ▸ (hI K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)
    · exact Or.inl hi
  · intro K _ φ hy X' π' f' hX κ _ _ D hD hc i
    let π : X' ⟶ B'.left := pullback.lift π' (f' ≫ Spec.map (CommRingCat.ofHom φ)) (by
      simp only [Category.assoc]
      exact hX.w)
    have hπ : IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hpb
      rw [pullback.lift_fst]
      exact hX
    have ht : Triv (F.pull π) := (test K φ X' π f' hπ).2 hy
    obtain ⟨w, hw⟩ := (CechPic.iso_triv_iff (F.pull π)).2 ht
    obtain ⟨e⟩ := c₄ K φ X' π f' hπ κ D hD hc i
    exact ⟨e.trans (HomologicalComplex.homologyMapIso
      (cechLBCongr f' D (LB.isLB_triv X') (pull_isLB hF π) w hw) i).symm.toLinearEquiv⟩

end GlobalTheory.MumfordLocalComplex

namespace GlobalTheory.MumfordLocalComplex

theorem exists_ideal_free_complex_at_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), L.IsLB → IsProjBy A.hom → (∃ t : LB.Gen (Theta A L), t.IsGen) → IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → (∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∃ (J : Ideal (A.left.presheaf.stalk x₀)) (C : CochainComplex (ModuleCat.{0} (A.left.presheaf.stalk x₀)) ℕ) (φ : A.left.presheaf.stalk x₀ →+* K), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) ∧ RingHom.ker φ = IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∧ (∀ i, Module.Free (A.left.presheaf.stalk x₀) (C.X i) ∧ Module.Finite (A.left.presheaf.stalk x₀) (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual (A.left.presheaf.stalk x₀) (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A.left.presheaf.stalk x₀] (A.left.presheaf.stalk x₀ ⧸ J)) ∧ (∀ p : PrimeSpectrum (A.left.presheaf.stalk x₀), ∃ (K' : Type) (_ : Field K') (φ' : A.left.presheaf.stalk x₀ →+* K'), RingHom.ker φ' = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∨ g < i) → (((ModuleCat.extendScalars φ').mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty (((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i) ≃ₗ[K] (cechLB A.hom (LB.triv A.left) D).homology i) := by
  intro K _ _ A _ g hA hg L H _ j hL hp hΘ _ hjc hfin hH x₀ hx₀
  have := hA.comm
  have := hA.smooth
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ A L hL
  let ηK : Sp K ⟶ A.left := (η[A]).left
  have hηK : ηK ≫ A.hom = 𝟙 _ := Over.w η[A]
  obtain ⟨e, rfl⟩ := hx₀
  obtain rfl : e = IsLocalRing.closedPoint K := @Subsingleton.elim (Sp K) inferInstance _ _
  let φ : A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K)) →+* K := (Scheme.stalkClosedPointTo ηK).hom
  have hφl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo ηK).hom)
  have hφa : Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) = ηK :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ηK
  have h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨z, hz⟩ := (hH (𝟙_ _) η[A]).1 (h1 ▸ memKL_one hL (𝟙_ (Over (Sp K))))
  have hy : ∃ y : Spec (CommRingCat.of K) ⟶ H.left,
      y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) :=
    ⟨z.left, by rw [hφa]; exact congrArg (·.left) hz⟩
  haveI hN : IsNoetherianRing (A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K))) := inferInstance
  obtain ⟨I, C, c₁, c₂, eC, c₃, hI, c₅⟩ := @exists_ideal_complex_cech globalFns_holds _ _ A _ _ hA hp g hg L _ hL hO hΘ hu H j
    (fun T x => (hK _ rfl T x).symm.trans (hH T x)) (A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K))) _ hN _
    (A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K))) K _ φ hφl hy
  refine ⟨I, C, φ, fun R' _ ψ => GlobalTheory.T.local_ring_points_ideal_criterion _ A.left H.left _ j.left hjc I hI R' ψ, ?_, c₁, c₂, eC,
    fun p => ?_, ?_⟩
  · exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (RingHom.ker_ne_top φ) fun x hx => by
      simpa [IsLocalRing.maximalIdeal_eq_bot] using map_nonunit φ x hx).symm
  · obtain ⟨K', _, φ', hk, hex⟩ := c₃ p.asIdeal p.isPrime
    refine ⟨K', inferInstance, φ', hk, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
    obtain ⟨y, hy'⟩ := (hI K' φ').2 (hk ▸ hIp)
    let q := Spec.map (CommRingCat.ofHom φ') (IsLocalRing.closedPoint K')
    have hq : q.asIdeal = RingHom.ker φ' := by
      show Ideal.comap φ' (IsLocalRing.maximalIdeal K') = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K')) =
        A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q :=
      congrArg (fun f => f (IsLocalRing.closedPoint K')) hy'
    have hc : IsClosed ({j.left (y (IsLocalRing.closedPoint K'))} : Set A.left) := by
      have := j.left.isClosedEmbedding.isClosedMap _
        (GlobalTheory.StabFlat.isClosed_of_isFinite H.hom (y (IsLocalRing.closedPoint K')) (Subsingleton.elim _ (IsLocalRing.closedPoint K)))
      rwa [Set.image_singleton] at this
    have hs : A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q ⤳ ηK (IsLocalRing.closedPoint K) := by
      have : A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q ∈
          Set.range (A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K))) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : ηK (IsLocalRing.closedPoint K) = A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q :=
      (hs.mem_closed hc e.symm).trans e
    have hq' : q = IsLocalRing.closedPoint _ := (A.left.fromSpecStalk _).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, ← hq, hq']
    rfl
  · intro κ _ _ D hD hc i
    have hsq : IsPullback (𝟙 A.left) A.hom A.hom
        (Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) ≫ A.hom) := by
      rw [← Category.assoc, hφa, hηK]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact c₅ K φ hy A.left (𝟙 _) A.hom hsq κ D hD hc i

end GlobalTheory.MumfordLocalComplex
