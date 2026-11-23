import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFiniteStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenLeOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientOfFiniteGroup
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientIsReducedIsNormalFlatStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverFiniteGroupQuotientStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientExistsUniqueCompEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace QuotModel

theorem isProjOver_comp_spMap {O O' : Type} [CommRing O] [CommRing O'] (b : O' →+* O) {X : Scheme.{0}}
    (s : X ⟶ Sp O) (hb : IsFinite (spMap b)) (hs : IsProjOver s) : IsProjOver (s ≫ spMap b) := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N b
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N b) := MorphismProperty.of_isPullback P.flip hb
  have := GlobalTheory.T.isProjOver_comp_finite O' (PSpace O' N) X (i ≫ GlobalTheory.ProjSpace.baseChange N b) (PSpace.str O' N) inferInstance
    ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  rwa [Category.assoc, P.w, ← Category.assoc] at this

theorem isPullback_fractionField {O O' F F' : Type} [CommRing O] [CommRing O'] [Field F] [Field F'] [IsDomain O]
    [Algebra O F] [IsFractionRing O F] [Algebra O' F'] [IsFractionRing O' F'] (b : O' →+* O) (k : F' →+* F)
    (h : (algebraMap O F).comp b = k.comp (algebraMap O' F')) (hb : IsFinite (spMap b)) :
    Function.Injective b ∧
      IsPullback (spMap (algebraMap O F)) (spMap k) (spMap b) (spMap (algebraMap O' F')) := by
  have hinj : Function.Injective b := by
    have : Function.Injective ((algebraMap O F).comp b) := by
      rw [h]; exact k.injective.comp (IsFractionRing.injective O' F')
    exact Function.Injective.of_comp (f := algebraMap O F) this
  refine ⟨hinj, ?_⟩
  have hfin : b.Finite := (IsFinite.SpecMap_iff _).mp hb
  letI := b.toAlgebra
  letI := ((algebraMap O F).comp b).toAlgebra
  have : IsScalarTower O' O F := .of_algebraMap_eq' rfl
  have : Module.Finite O' O := hfin
  have : FaithfulSMul O' O := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Nontrivial O' := b.domain_nontrivial
  have : Algebra.IsAlgebraic O' O := inferInstance
  have h1 : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors O')) F := inferInstance
  have h2 : IsLocalization ((nonZeroDivisors O').map b) F := h1
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization b k h.symm (nonZeroDivisors O'))

theorem exists_isOpenImmersion_quotient (Γ : Type) [Group Γ] [Finite Γ] (Y Y' U U' : Scheme.{0}) (τ : Γ →* Aut Y)
    (ρ₀ : Γ →* Aut U) (φ : Y ⟶ Y') (r : U ⟶ U') (j : U ⟶ Y) [IsOpenImmersion j]
    (hφ : (IsAffineHom φ ∧ (∀ g, (τ g).hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom))
    (hr : (IsAffineHom r ∧ (∀ g, (ρ₀ g).hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom))
    (hj : ∀ g, j ≫ (τ g).hom = (ρ₀ g).hom ≫ j) :
    ∃ j' : U' ⟶ Y', IsOpenImmersion j' ∧ r ≫ j' = j ≫ φ ∧ φ ⁻¹' Set.range j' = Set.range j := by
  have hst : ∀ g (y : Y), y ∈ j.opensRange → (τ g).hom y ∈ j.opensRange := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨(ρ₀ g).hom u, by rw [← Scheme.Hom.comp_apply, ← hj, Scheme.Hom.comp_apply]⟩
  obtain ⟨V, hV⟩ := (quotient_isIntegral_surjective_orbits Γ Y Y' τ φ hφ).2.2.2.2 j.opensRange (by
    intro g
    ext y
    refine ⟨fun h => ?_, hst g y⟩
    have h1 := hst g⁻¹ _ h
    have e : (τ g).hom ≫ (τ g⁻¹).hom = 𝟙 Y := by
      rw [map_inv]; exact (τ g).hom_inv_id
    rwa [← Scheme.Hom.comp_apply, e] at h1)
  let φ' : U ⟶ V := IsOpenImmersion.lift V.ι (j ≫ φ) (by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : j u ∈ φ ⁻¹ᵁ V := by rw [hV]; exact ⟨u, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact this)
  have e : φ' ≫ V.ι = j ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have P : IsPullback φ' j V.ι φ := IsOpenImmersion.isPullback _ _ _ _ e.symm (by
    rw [Scheme.Opens.opensRange_ι, hV])
  have hφ' := (quotient_flat_baseChange Γ Y Y' U V τ φ φ' j V.ι hφ P inferInstance).2 ρ₀ fun g =>
    ⟨by rw [← cancel_mono V.ι, Category.assoc, e, ← Category.assoc, ← hj, Category.assoc, hφ.2.1], (hj g).symm⟩
  obtain ⟨a, ha, -⟩ := quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr V φ' hφ'.2.1
  obtain ⟨a', ha', -⟩ := quotient_existsUnique_comp_eq Γ U V ρ₀ φ' hφ' U' r hr.2.1
  have : IsIso a := ⟨a', (quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr U' r hr.2.1).unique
    (by rw [← Category.assoc, ha, ha']) (Category.comp_id _),
    (quotient_existsUnique_comp_eq Γ U V ρ₀ φ' hφ' V φ' hφ'.2.1).unique
    (by rw [← Category.assoc, ha', ha]) (Category.comp_id _)⟩
  refine ⟨a ≫ V.ι, inferInstance, by rw [← Category.assoc, ha, e], ?_⟩
  have hr' : Set.range (a ≫ V.ι) = V := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, a.surjective.range_comp, Scheme.Opens.range_ι]
  rw [hr']
  exact congrArg SetLike.coe hV

end QuotModel

theorem exists_quotient_model_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (Γ : Type) [Group Γ] [Finite Γ] (C : Cpt c t β) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (β' : O' →+* F') (b : O' →+* O) (k : F' →+* F) (r : U ⟶ U') (ρ₀ : Γ →* Aut U) (ρ : Γ →* Aut C.X), IsDedFrac β → IsDedFrac β' → β.comp b = k.comp β' → IsFinite (spMap b) → r ≫ c' = c ≫ spMap k → (IsAffineHom r ∧ (∀ g, (ρ₀ g).hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ₀ g).hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ₀ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → (∀ g, C.j ≫ (ρ g).hom = (ρ₀ g).hom ≫ C.j) → ∃ (X' : Scheme.{0}) (π : C.X ⟶ X') (s' : X' ⟶ Sp O') (jQ : U' ⟶ pullback s' (spMap β')), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(C.X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) ∧ IsFinite π ∧ π ≫ s' = C.s ≫ spMap b ∧ Geo.Tor.IsNormalScheme X' ∧ IsProjOver s' ∧ Flat s' ∧ jQ ≫ pullback.snd _ _ = c' ∧ IsOpenImmersion jQ ∧ Dense (Set.range jQ) ∧ r ≫ jQ ≫ pullback.fst _ _ = C.j ≫ π ∧ ∀ x : C.X, π x ∈ Set.range (jQ ≫ pullback.fst s' (spMap β')) ↔ x ∈ Set.range C.j := by
  intro E _ _ _ H U F O _ _ c t β Γ _ _ C U' F' O' _ _ c' β' b k r ρ₀ ρ hβ hβ' hbk hb hrc hr hρ
  obtain ⟨⟨_, _⟩, -, hF⟩ := hβ
  obtain ⟨⟨_, _⟩, -, hF'⟩ := hβ'
  letI := β.toAlgebra
  letI := β'.toAlgebra
  obtain ⟨hN, hC, hS, hpre, hfl, hdom, hqc⟩ :=
    genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hdom' : IsDominant C.j := hdom
  obtain ⟨hinj, Pb⟩ := QuotModel.isPullback_fractionField (F := F) (F' := F') b k hbk hb
  replace Pb : IsPullback (spMap β) (spMap k) (spMap b) (spMap β') := Pb
  have hred : IsReduced C.X := by
    have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
      have := (C.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hjs : C.j ≫ C.s ≫ spMap b = r ≫ c' ≫ spMap β' := by
    rw [Cpt.j, Category.assoc, pullback.condition_assoc, ← Category.assoc, C.jQ_over, Pb.w, reassoc_of% hrc]
  have hinv : ∀ g, (ρ g).hom ≫ C.s ≫ spMap b = C.s ≫ spMap b := fun g =>
    ext_of_isDominant C.j (by rw [← Category.assoc, hρ, Category.assoc, hjs, ← Category.assoc, hr.2.1])
  have hproj := QuotModel.isProjOver_comp_spMap b C.s hb C.proj
  have hq : IsQProjOver C.s := by
    obtain ⟨N, i, hi, e⟩ := C.proj
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  obtain ⟨X', π, hπ⟩ := exists_quotient_of_finite_group Γ C.X ρ fun x => by
    obtain ⟨V, hV, h, -⟩ := exists_isAffineOpen_le_of_isQProjOver O C.X C.s hq
      (Set.range fun g => (ρ g).hom x) ⊤ (Set.finite_range _) (Set.subset_univ _)
    exact ⟨V, hV, fun g => h ⟨g, rfl⟩⟩
  obtain ⟨s', hs', -⟩ := quotient_existsUnique_comp_eq Γ C.X X' ρ π hπ _ _ hinv
  have hprop : IsProper (π ≫ s') := by
    obtain ⟨N, i, hi, e⟩ := hproj
    have := isProper_str O' N
    rw [hs', ← e]; infer_instance
  have hfin := (GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties Γ C.X X' ρ π hπ _ s' inferInstance).1
  obtain ⟨-, hnorm, hflat⟩ := GlobalTheory.T.quotient_isReduced_isNormal_flat_of_invariant_sections Γ C.X X' ρ π hπ
  have hbf : Flat (spMap b) := by
    rw [Flat.SpecMap_iff]
    letI := b.toAlgebra
    have : FaithfulSMul O' O := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat O' O)
  have hs'f : Flat s' := hflat O' s' (by rw [hs']; have := C.flat; infer_instance)
  have hβf : Flat (spMap β') := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F' (nonZeroDivisors O'))
  have hβm : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  let p := pullback.fst C.s (spMap β)
  let p' := pullback.fst s' (spMap β')
  have hpm : IsPreimmersion p :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hβm
  let φ : pullback C.s (spMap β) ⟶ pullback s' (spMap β') :=
    pullback.lift (p ≫ π) (pullback.snd _ _ ≫ spMap k) (by
      rw [Category.assoc, hs', pullback.condition_assoc, Pb.w, Category.assoc])
  have e1 : φ ≫ p' = p ≫ π := pullback.lift_fst _ _ _
  have e2 : φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := pullback.lift_snd _ _ _
  have P : IsPullback φ p p' π := by
    refine IsPullback.of_right ?_ e1 (IsPullback.of_hasPullback s' (spMap β')).flip
    rw [e2, hs']
    exact ((IsPullback.of_hasPullback C.s (spMap β)).paste_vert Pb).flip
  obtain ⟨⟨τ, hτ⟩, hφ⟩ := quotient_flat_baseChange Γ C.X X' _ _ ρ π φ p p' hπ P inferInstance
  replace hφ := hφ τ hτ
  have := C.jQ_open
  obtain ⟨j', hj', e3, e4⟩ := QuotModel.exists_isOpenImmersion_quotient Γ _ _ U U' τ ρ₀ φ r C.jQ hφ hr fun g => by
    rw [← cancel_mono p, Category.assoc, (hτ g).2, ← Category.assoc, Category.assoc (ρ₀ g).hom]
    exact hρ g
  have e5 : r ≫ j' ≫ p' = C.j ≫ π := by
    rw [reassoc_of% e3, e1, Cpt.j, Category.assoc]
  refine ⟨X', π, s', j', hπ, hfin, hs', hnorm hN C.normal, GlobalTheory.T.isProjOver_finite_group_quotient Γ C.X X' ρ π hπ O' s' (hs' ▸ hproj), hs'f,
    ?_, hj', ?_, e5, fun x => ⟨?_, ?_⟩⟩
  · refine (quotient_existsUnique_comp_eq Γ U U' ρ₀ r hr _ (r ≫ c') fun g => ?_).unique ?_ rfl
    · rw [← Category.assoc, hr.2.1]
    · rw [reassoc_of% e3, e2, ← Category.assoc, C.jQ_over, hrc]
  · have hsurj := (quotient_isIntegral_surjective_orbits Γ _ _ τ φ hφ).2.1
    have hd : Dense (φ '' Set.range C.jQ) := φ.surjective.denseRange.dense_image φ.continuous C.jQ_dense
    exact hd.mono (by rw [← e4]; exact Set.image_preimage_subset _ _)
  · rintro ⟨u, hu⟩
    obtain ⟨y, hy, rfl⟩ := Scheme.exists_preimage_of_isPullback P (j' u) x
      (by rw [← hu, Scheme.Hom.comp_apply])
    have : y ∈ Set.range C.jQ := by rw [← e4]; exact ⟨u, hy.symm⟩
    obtain ⟨v, rfl⟩ := this
    exact ⟨v, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨u, rfl⟩
    exact ⟨r u, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e5]⟩

end GlobalTheory
