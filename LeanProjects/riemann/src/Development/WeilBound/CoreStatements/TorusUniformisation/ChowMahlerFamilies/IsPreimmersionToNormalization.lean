import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.StratumOpenCover

theorem isPreimmersion_val (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    (L : Type) [Field L] [Algebra A L] [Algebra.IsAlgebraic A L]
    (hinj : Function.Injective (algebraMap A L)) (e : L ≃ₐ[A] B) :
    IsPreimmersion (Spec.map (CommRingCat.ofHom (integralClosure A B).val.toRingHom)) := by
  have hB : IsField B := MulEquiv.isField (Field.toIsField L) e.symm.toMulEquiv
  let : Field B := hB.toField
  have : Algebra.IsAlgebraic A B := e.isAlgebraic
  have : IsFractionRing (integralClosure A B) B :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := B) fun x hx => by
      apply hinj
      apply e.injective
      simpa using hx
  exact IsPreimmersion.of_isLocalization (R := integralClosure A B) (S := B) (nonZeroDivisors _)

theorem isPreimmersion_toNormalization (Z : Scheme.{0}) [IsIntegral Z] {L : Type} [Field L]
    (φ : Z.presheaf.stalk (genericPoint Z) ⟶ .of L) (hφ : φ.hom.Finite) :
    IsPreimmersion (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)).toNormalization := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint Z)) isOpen_univ
  set f := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) with hf
  have htop : f ⁻¹ᵁ U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    change f x ∈ U
    rw [hf, Scheme.Hom.comp_apply]
    have : Z.fromSpecStalk (genericPoint Z) (Spec.map φ x) ∈
        Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hxU
  let := (f.app U).hom.toAlgebra
  let ψ : CommRingCat.of L ⟶ Γ(Spec (.of L), f ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso (.of L)).inv ≫ (Spec (.of L)).presheaf.map (homOfLE le_top).op
  have : IsIso (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)) := ⟨homOfLE htop.ge, rfl, rfl⟩
  have hψ : IsIso ψ := inferInstance
  have happ : f.app U = Z.presheaf.germ U _ hxU ≫ φ ≫ ψ := by
    simp only [f, ψ, Scheme.Hom.comp_app, Scheme.fromSpecStalk_app hxU, Category.assoc]
    rw [Scheme.Hom.naturality, Scheme.ΓSpecIso_inv_naturality_assoc φ]
    rfl
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let : Algebra Z.functionField L := φ.hom.toAlgebra
  let : Algebra Γ(Z, U) L := (Z.presheaf.germ U _ hxU ≫ φ).hom.toAlgebra
  have : IsScalarTower Γ(Z, U) Z.functionField L := .of_algebraMap_eq fun _ => rfl
  have : IsFractionRing Γ(Z, U) Z.functionField := functionField_isFractionRing_of_isAffineOpen Z U hU
  have : Module.Finite Z.functionField L := hφ
  have : Algebra.IsAlgebraic Γ(Z, U) L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := Z.functionField)).mpr inferInstance
  have hinj : Function.Injective (algebraMap Γ(Z, U) L) := by
    rw [IsScalarTower.algebraMap_eq Γ(Z, U) Z.functionField L]
    exact (algebraMap Z.functionField L).injective.comp (IsFractionRing.injective _ _)
  let e : L ≃ₐ[Γ(Z, U)] Γ(Spec (.of L), f ⁻¹ᵁ U) :=
    { (asIso ψ).commRingCatIsoToRingEquiv with
      commutes' := fun a => by
        change ((Z.presheaf.germ U _ hxU ≫ φ) ≫ ψ).hom a = (f.app U).hom a
        rw [happ, Category.assoc] }
  have h1 := isPreimmersion_val Γ(Z, U) Γ(Spec (.of L), f ⁻¹ᵁ U) L hinj e
  have h2 := f.ι_toNormalization ⟨U, hU⟩
  have hW : IsAffineOpen (f ⁻¹ᵁ U) := htop ▸ isAffineOpen_top _
  have h3 : IsIso (f ⁻¹ᵁ U).toSpecΓ := by
    rw [← hW.isoSpec_hom]; infer_instance
  have h4 : IsIso (f ⁻¹ᵁ U).ι := by
    rw [htop]; exact inferInstanceAs (IsIso (Spec (.of L)).topIso.hom)
  have h5 : IsPreimmersion ((f ⁻¹ᵁ U).ι ≫ f.toNormalization) := by
    rw [h2]
    have h7 : IsOpenImmersion (f.normalizationOpenCover.f ⟨U, hU⟩) := f.normalizationOpenCover.map_prop _
    have h8 : IsPreimmersion (f.normalizationOpenCover.f ⟨U, hU⟩) :=
      (fun {X Y : Scheme.{0}} (g : X ⟶ Y) (_ : IsOpenImmersion g) => (inferInstance : IsPreimmersion g)) _ h7
    exact @IsPreimmersion.comp _ _ _ _ _ inferInstance (@IsPreimmersion.comp _ _ _ _ _ h1 h8)
  have h6 : IsPreimmersion (inv (f ⁻¹ᵁ U).ι ≫ (f ⁻¹ᵁ U).ι ≫ f.toNormalization) := inferInstance
  rwa [IsIso.inv_hom_id_assoc] at h6

end PositivityTheory.Xgn.StratumOpenCover

theorem PositivityTheory.Xgn.stratum_finite_normal_cover : ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (L : Type) [Field L] (z : Sp L ⟶ Z), GlobalTheory.IsGenericPointHom z → ∀ (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L'], ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (j : Sp L' ⟶ Z'), IsFinite π ∧ Surjective π ∧ IsNormalScheme Z' ∧ GlobalTheory.IsGenericPointHom j ∧ j ≫ π = spMap (algebraMap L L') ≫ z := by
  intro Z _ s _ _ L _ z hz L' _ _ _
  obtain ⟨e, rfl⟩ := hz
  obtain ⟨χ, hχ⟩ := Spec.map_surjective e.hom
  have : IsIso (Spec.map χ) := hχ ▸ inferInstance
  have hχ' : IsIso χ := (isIso_SpecMap_iff).mp this |> (ConcreteCategory.isIso_iff_bijective χ).mpr
  let φ : Z.presheaf.stalk (genericPoint Z) ⟶ .of L' := χ ≫ CommRingCat.ofHom (algebraMap L L')
  have hφ : φ.hom.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso χ).2)
  have hf : spMap (algebraMap L L') ≫ e.hom ≫ Z.fromSpecStalk (genericPoint Z) =
      Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) := by
    rw [← hχ, Spec.map_comp, Category.assoc]
  rw [hf]
  have : CharZero L' := by
    obtain ⟨ρ, -⟩ := Spec.map_surjective (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) ≫ s)
    exact charZero_of_injective_ringHom (R := ℚ) ρ.hom.injective
  have hfin := GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s (genericPoint Z) φ
    hφ.finiteType.essFiniteType
  have hpre := PositivityTheory.Xgn.StratumOpenCover.isPreimmersion_toNormalization Z φ hφ
  have hdom : IsDominant (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) := by
    refine ⟨?_⟩
    have hx : (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint L') =
        genericPoint Z := by
      have : Z.fromSpecStalk (genericPoint Z) (Spec.map φ (IsLocalRing.closedPoint L')) ∈
        Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨_, rfl⟩
      rw [Scheme.range_fromSpecStalk] at this
      exact (Specializes.antisymm this (genericPoint_specializes _)).eq
    refine Dense.mono (Set.singleton_subset_iff.mpr ⟨_, hx⟩) ?_
    exact dense_iff_closure_eq.mpr (genericPoint_spec Z)
  set f := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact hdom
  have : IsDominant f.fromNormalization := .of_comp f.toNormalization _
  refine ⟨f.normalization, inferInstance, f.fromNormalization, f.toNormalization, hfin,
    inferInstance, GlobalTheory.IsNormalScheme.pred _, GlobalTheory.IsGenericPointHom.of_isPreimmersion _,
    Scheme.Hom.toNormalization_fromNormalization _⟩
