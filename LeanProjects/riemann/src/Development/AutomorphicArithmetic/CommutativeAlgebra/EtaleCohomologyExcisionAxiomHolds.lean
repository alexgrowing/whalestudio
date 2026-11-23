import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EquivOfStalkwiseBaseChange
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistFinitary
import Development.AutomorphicArithmetic.CommutativeAlgebra.RedShDefs
import Development.AutomorphicArithmetic.CommutativeAlgebra.CechNervePullbackRepresentableOfIsPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SheafConnectedOfLevelwiseConnected
import Development.AutomorphicArithmetic.CommutativeAlgebra.CechAugmentationEquivOfSection
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionOfIntegralSurjectiveAlgClosed
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCyclotomicRootOfStrictHenselian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsTateTwistSectionsEquivLocallyConstant
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyConstantComapBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUniqueIdempotentLiftTensorFieldStrictHense
import Development.AutomorphicArithmetic.CommutativeAlgebra.AcyclicSpecIntegralAlgebraStrictHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private theorem bijective_pull_spMap_tw_zero : ∀ (q : ℕ) [NeZero q] (i : ℤ) (B B' : Type) [CommRing B] [CommRing B'] (φ : B →+* B'), IsUnit (q : B) →
    (∃ ζ : B, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) →
    (∀ e' : B', IsIdempotentElem e' → ∃! e : B, IsIdempotentElem e ∧ φ e = e') →
    Function.Bijective (pull _ (spMap φ) (tw q i) 0) := by
  intro q _ i B B' _ _ φ hq ⟨ζ, hζ⟩ hid
  obtain ⟨E, hE⟩ := UpperTheory.exists_tateTwist_sections_equiv_locallyConstant q i
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)
  let g : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom φ)
  let ζ₀ : Prim q Γ(Spec (CommRingCat.of B), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ⟨ζ, hq, hζ⟩
  have hres : Function.Bijective (Sec.res (F := tw q i) g) := by
    have h1 := UpperTheory.locallyConstant_comap_bijective B B' φ (ZMod q) hid
    have hc : ∀ s, E _ (ζ₀.map g.appTop.hom) (Sec.res g s) = (E _ ζ₀ s).comap ⟨g, g.continuous⟩ := hE _ _ g ζ₀
    have hcomp : (E _ (ζ₀.map g.appTop.hom)) ∘ (Sec.res (F := tw q i) g) = (fun a : LocallyConstant (PrimeSpectrum B) (ZMod q) => a.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩) ∘ (E _ ζ₀) := by
      funext s
      exact hc s
    refine (Function.Bijective.of_comp_iff' (E _ (ζ₀.map g.appTop.hom)).bijective _).1 ?_
    rw [hcomp]
    exact h1.comp (E _ ζ₀).bijective
  have hp : (pull _ (sch.map g) (tw q i) 0) ∘ (e _) = (e _) ∘ (Sec.res (F := tw q i) g) := by
    funext s
    exact he g s
  refine (Function.Bijective.of_comp_iff _ (e _).bijective).1 ?_
  rw [hp]
  exact (e _).bijective.comp hres

private theorem eqv_ring : ∀ (q : ℕ) (O R K : Type) [CommRing O] [CommRing R] [Field K] [Algebra O R] [Algebra O K]
    [Algebra.IsIntegral O R] [Algebra.IsIntegral O K], SH O → IsUnit (q : O) → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[O] K)) (tw q i) := by
  intro q O R K _ _ _ _ _ _ _ hSH hq i n
  obtain ⟨hH, -⟩ := id hSH
  haveI : NeZero q := ⟨by
    rintro rfl
    simp at hq⟩
  have hqR : IsUnit (q : R) := by simpa using hq.map (algebraMap O R)
  haveI : Algebra.IsIntegral O (R ⊗[O] K) := by
    have : Algebra.IsIntegral R (R ⊗[O] K) := inferInstance
    exact Algebra.IsIntegral.trans R
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hs := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1
    haveI := hs (sp R) n hn
    haveI := hs (sp (R ⊗[O] K)) n hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · obtain ⟨ζ, hζ⟩ := UpperTheory.exists_cyclotomic_root_of_strictHenselian q O hSH hq
    refine bijective_pull_spMap_tw_zero q i R _ _ hqR ⟨algebraMap O R ζ, ?_⟩ (UpperTheory.existsUnique_idempotent_lift_tensor_field_strictHenselian O R K hSH)
    rw [Polynomial.aeval_algebraMap_apply, hζ, map_zero]
  · haveI := UpperTheory.acyclic_spec_integral_algebra_strictHenselian q O R hSH hq n i hn
    haveI := UpperTheory.acyclic_spec_integral_algebra_strictHenselian q O (R ⊗[O] K) hSH hq n i hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

private theorem T_key : ∀ (q : ℕ) (O K : Type) [CommRing O] [Field K] [Algebra O K] [Algebra.IsIntegral O K], SH O → IsUnit (q : O) →
    ∀ (i : ℤ) {Z Z' W : Scheme.{0}} (r : Z ⟶ W) [IsIntegralHom r] (e : W ≅ Spec (CommRingCat.of O)) (c : Z' ⟶ Z)
      (g' : Z' ⟶ Spec (CommRingCat.of K)),
      IsPullback c g' r (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ e.inv) → Eqv _ (sch.map c) (tw q i) := by
  intro q O K _ _ _ _ hSH hq i Z Z' W r _ e c g' hpb
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hg : IsIntegralHom (r ≫ e.hom) := inferInstance
  haveI : IsAffine Z := isAffine_of_isAffineHom (r ≫ e.hom)
  let φ : CommRingCat.of O ⟶ Γ(Z, ⊤) := Spec.preimage (Z.isoSpec.inv ≫ r ≫ e.hom)
  have hφ : Spec.map φ = Z.isoSpec.inv ≫ r ≫ e.hom := Spec.map_preimage _
  letI alg : Algebra O Γ(Z, ⊤) := φ.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap O Γ(Z, ⊤))) = Z.isoSpec.inv ≫ r ≫ e.hom := hφ
  haveI hint : Algebra.IsIntegral O Γ(Z, ⊤) := by
    have h2 : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap O Γ(Z, ⊤)))) := by
      rw [hmap]; infer_instance
    rw [IsIntegralHom.SpecMap_iff] at h2
    exact (algebraMap_isIntegral_iff (R := O) (A := Γ(Z, ⊤))).1 h2
  have sq1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O Γ(Z, ⊤) K)
  have sq2 : IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K)) ≫ Z.isoSpec.inv) (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := Γ(Z, ⊤)) (B := K)).toRingHom)) (r ≫ e.hom) (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
    refine IsPullback.of_iso sq1 (Iso.refl _) Z.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [hmap]
    · simp
  have sq3 : IsPullback c g' (r ≫ e.hom) (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
    refine IsPullback.of_iso hpb (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
  obtain ⟨u, hu⟩ : ∃ u : Z' ≅ Spec (CommRingCat.of (Γ(Z, ⊤) ⊗[O] K)), u.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K)) ≫ Z.isoSpec.inv = c :=
    ⟨_, sq3.isoIsPullback_hom_fst _ _ sq2⟩
  have hE := eqv_ring q O Γ(Z, ⊤) K hSH hq i
  have h1 : sch.map c ≫ sch.map Z.isoSpec.hom = sch.map u.hom ≫ spMap (Algebra.TensorProduct.includeLeftRingHom : Γ(Z, ⊤) →+* Γ(Z, ⊤) ⊗[O] K) := by
    rw [← sch.map_comp, ← sch.map_comp, ← hu]
    simp
  have h2 : Eqv _ (sch.map c ≫ sch.map Z.isoSpec.hom) (tw q i) := by
    rw [h1]
    exact (hcomp _ _ _ _ _).1 (hiso _ _ _ inferInstance) hE
  exact (hcomp _ _ _ _ _).2.2 (hiso _ _ _ inferInstance) h2

private theorem eqv_of_forall_conn {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {F : Shv R}
    (h : ∀ m, UpperTheory.RedSh.Conn f F m) : Eqv R f F := fun n => (h (n + 1)).1 n (by omega)

private theorem conn_of_eqv {R : Type} [CommRing R] {E E' : Spc} {f : E ⟶ E'} {F : Shv R}
    (h : Eqv R f F) (m : ℤ) : UpperTheory.RedSh.Conn f F m := ⟨fun n _ => h n, (h m).1⟩

private theorem L_loc : ∀ (q : ℕ) (O : Type) [CommRing O], SH O → IsUnit (q : O) → ∀ (i : ℤ) {Y W : Scheme.{0}} (g : Y ⟶ W)
    [IsIntegralHom g] [Surjective g] (e : W ≅ Spec (CommRingCat.of O)), Eqv _ (cechAug g) (tw q i) := by
  intro q O _ hSH hq i Y W g _ _ e
  obtain ⟨hH, hS⟩ := id hSH
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  haveI : Algebra.IsIntegral O (IsLocalRing.ResidueField O) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId O (IsLocalRing.ResidueField O)) IsLocalRing.residue_surjective
  haveI : Algebra.IsIntegral O K := Algebra.IsIntegral.trans (IsLocalRing.ResidueField O)
  let b : Spec (CommRingCat.of K) ⟶ W := Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ e.inv
  have hpb := IsPullback.of_hasPullback g b
  haveI : IsIntegralHom (pullback.snd g b) := MorphismProperty.of_isPullback hpb inferInstance
  haveI : Surjective (pullback.snd g b) := MorphismProperty.of_isPullback hpb inferInstance
  obtain ⟨s, hs⟩ := UpperTheory.exists_section_of_integral_surjective_algClosed K (pullback.snd g b)
  have hsplit : Eqv _ (cechAug (pullback.snd g b)) (tw q i) := UpperTheory.cechAugmentation_equiv_of_section _ _ s hs _
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ _ _ _ _ hpb
  have hb : Eqv _ (sch.map b) (tw q i) := by
    have : IsPullback b (𝟙 _) (𝟙 W) b := IsPullback.of_vert_isIso ⟨by simp⟩
    exact T_key q O K hSH hq i (𝟙 W) e b (𝟙 _) this
  have hlev : Eqv _ m (tw q i) := by
    refine eqv_of_forall_conn fun n => UpperTheory.sheafConnected_of_levelwise_connected _ _ m n fun k => conn_of_eqv ?_ _
    obtain ⟨Z, π, ez, hπ, hz⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ g inferInstance (op (SimplexCategory.mk k))
    have hpz := IsPullback.of_hasPullback (π ≫ g) b
    obtain ⟨ez', hez'⟩ := UpperTheory.cechNerve_pullback_representable_of_isPullback g (pullback.snd g b) b m hm (op (SimplexCategory.mk k)) ez (π ≫ g)
      (pullback.fst (π ≫ g) b) (pullback.snd (π ≫ g) b) hz hpz
    have h1 : Eqv _ (sch.map (pullback.fst (π ≫ g) b)) (tw q i) :=
      T_key q O K hSH hq i (π ≫ g) e _ _ hpz
    have h3 : Eqv _ (disc.map ez'.hom ≫ disc.map (m.app (op (SimplexCategory.mk k)))) (tw q i) := by
      rw [← Functor.map_comp, hez', Functor.map_comp]
      exact (hcomp _ _ _ _ _).1 h1 (hiso _ _ _ inferInstance)
    exact (hcomp _ _ _ _ _).2.1 (hiso _ _ _ inferInstance) h3
  have hc : m ≫ cechAug g = cechAug (pullback.snd g b) ≫ sch.map b := hm.w
  have h2 : Eqv _ (m ≫ cechAug g) (tw q i) := by
    rw [hc]; exact (hcomp _ _ _ _ _).1 hsplit hb
  exact (hcomp _ _ _ _ _).2.1 hlev h2

theorem UpperTheory.etaleCohomology_excisionAxiom_holds : GlobalTheory.EtC.B4 := by
  intro q Y X f _ _ hq i
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hqc₁ : QcqsOver (cechAug f ≫ sch.map (𝟙 X)) := by
    intro k
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ f inferInstance k
    refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
    rw [sch.map_id, Category.comp_id]
    exact he
  have hqc₂ : QcqsOver (sch.map (𝟙 X)) := by
    intro k
    refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
    rw [sch.map_id]
    simp
    rfl
  refine UpperTheory.Cb.equiv_of_stalkwise_base_change _ (tw q i) X (cech f) (sch.obj X) (cechAug f) (sch.map (𝟙 X)) (UpperTheory.Cb.tateTwist_finitary q i)
    hqc₁ hqc₂ ?_
  intro O _ s hs
  obtain ⟨e₁, e₂, h⟩ := GlobalTheory.T.baseChange_cechNerveAugmentation_iso X X Y (𝟙 X) f (Over.mk s)
  have hO : IsUnit (q : O) := by
    simpa using (hq.map s.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom
  let w : pullback (𝟙 X) (Over.mk s).hom ≅ Spec (CommRingCat.of O) := asIso (pullback.snd _ _)
  have hfst : IsPullback (pullback.fst f (pullback.fst (𝟙 X) (Over.mk s).hom)) (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) f (pullback.fst (𝟙 X) (Over.mk s).hom) := IsPullback.of_hasPullback _ _
  haveI : IsIntegralHom (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) := MorphismProperty.of_isPullback hfst inferInstance
  haveI : Surjective (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom)) := MorphismProperty.of_isPullback hfst inferInstance
  have h2 : Eqv _ (cechAug (pullback.snd f (pullback.fst (𝟙 X) (Over.mk s).hom))) (tw q i) :=
    L_loc q O hs.1 hO i _ w
  have h3 : Eqv _ (e₁.hom ≫ (bcMap (cechAug f) (sch.map (𝟙 X))).app (Over.mk s)) (tw q i) := by
    rw [h]
    exact (hcomp _ _ _ _ _).1 h2 (hiso _ _ _ inferInstance)
  exact (hcomp _ _ _ _ _).2.1 (hiso _ _ _ inferInstance) h3
