import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullbackDegree.EpsPullbackFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.HasGoodReductionOfInertiaFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace UpperTheory.Lit.Nos.C6
open GlobalTheory

def basePtEquiv {K L : Type} [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] :
    (ptOver K L ⟶ A) ≃* (𝟙_ (Over (Sp L)) ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) :=
  let e : (Over.map (spMap (algebraMap K L))).obj (𝟙_ (Over (Sp L))) ≅ ptOver K L :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ spMap (algebraMap K L) = 𝟙 _ ≫ spMap (algebraMap K L)
      rfl)
  { toFun := fun x => (Over.mapPullbackAdj (spMap (algebraMap K L))).homEquiv _ A (e.hom ≫ x)
    invFun := fun y => e.inv ≫ ((Over.mapPullbackAdj (spMap (algebraMap K L))).homEquiv _ A).symm y
    left_inv := fun x => by simp
    right_inv := fun y => by simp
    map_mul' := fun x y => by
      rw [MonObj.comp_mul, ReciprocityTheory.ChartRestriction.G.Out.UBC.homEquiv_mul] }

def fixedPtHom {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] :
    (ptOver K (IntermediateField.fixedField H) ⟶ A) →* (ptOver K Ω ⟶ A) :=
  MonoidHom.mk' (fun x => ptOverMap (IntermediateField.val _) ≫ x) fun x y => MonObj.comp_mul _ x y

theorem fixedPtHom_injective {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] : Function.Injective (fixedPtHom H A) := by
  intro x y e
  have := epi_ptOverMap (IntermediateField.val (IntermediateField.fixedField H))
  exact Over.OverMorphism.ext ((cancel_epi (ptOverMap (IntermediateField.val _)).left).1
    (by simpa using congrArg (fun q => q.left) (show ptOverMap (IntermediateField.val _) ≫ x =
      ptOverMap (IntermediateField.val _) ≫ y from e)))

theorem card_torsion_fixedField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) [GrpObj A] (hA : LocallyOfFiniteType A.hom) (m : ℕ)
    (hfix : ∀ σ ∈ H, ∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → specAut σ ≫ x = x) :
    Nat.card {x : 𝟙_ (Over (Sp (IntermediateField.fixedField H))) ⟶
        (Over.pullback (spMap (algebraMap K (IntermediateField.fixedField H)))).obj A // x ^ m = 1} =
      Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} := by
  have e1 := Equiv.subtypeEquiv (basePtEquiv (K := K) (L := IntermediateField.fixedField H) A).symm.toEquiv
    (p := fun x => x ^ m = 1) (q := fun y => y ^ m = 1) (fun x => by
      change x ^ m = 1 ↔ (basePtEquiv A).symm x ^ m = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  rw [Nat.card_congr e1]
  refine Nat.card_eq_of_bijective (fun y => ⟨fixedPtHom H A y.1, by rw [← map_pow, y.2, map_one]⟩) ⟨?_, ?_⟩
  · intro y y' h
    exact Subtype.ext (fixedPtHom_injective H A (congrArg Subtype.val h))
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_fixedField_point_of_fixed_by_subgroup K Ω H A hA z (fun σ hσ => hfix σ hσ z hz)
    have hep := epi_ptOverMap (IntermediateField.val (IntermediateField.fixedField H))
    have hj : (ptOverMap (IntermediateField.val (IntermediateField.fixedField H))).left =
        spMap (algebraMap (IntermediateField.fixedField H) Ω) := rfl
    rw [hj] at hep
    have hover : y ≫ A.hom = spMap (algebraMap K (IntermediateField.fixedField H)) := by
      refine (cancel_epi (spMap (algebraMap (IntermediateField.fixedField H) Ω))).1 ?_
      rw [← Category.assoc, hy, Over.w z]
      change spMap (algebraMap K Ω) = _
      rw [← Spec.map_comp]
      congr 1
    let y' : ptOver K (IntermediateField.fixedField H) ⟶ A := Over.homMk y hover
    have hy' : fixedPtHom H A y' = z := Over.OverMorphism.ext hy
    refine ⟨⟨y', ?_⟩, Subtype.ext hy'⟩
    apply fixedPtHom_injective H A
    rw [map_pow, hy', hz, map_one]

end UpperTheory.Lit.Nos.C6

namespace UpperTheory.Lit.Nos.C6
open GlobalTheory

theorem hasGoodReduction_of_infinite_torsionUnramified : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite → HasGoodReduction R K A := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA hinf
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  apply UpperTheory.Lit.Nos.C5.hasGoodReduction_of_inertiaFixed R K Ω V hV A hA
  obtain ⟨hSH, f, -, -⟩ := GlobalTheory.T.inertiaFixedField_valuationRing_strictlyHenselian R K Ω V hV
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelianVariety_field K A hA
  have hA' := isAbelianScheme_pullback_obj (spMap (algebraMap K (IntermediateField.fixedField (inertia K V)))) A hA
  haveI := hA'.comm
  have hloc : LocallyOfFiniteType A.hom := by haveI := hA.smooth; infer_instance
  refine GlobalTheory.T.hasGoodReduction_of_many_rational_torsion_points _ _ hSH _ hA' g ?_ ?_
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  · refine hinf.mono ?_
    rintro m ⟨hm, hu⟩
    have hunit : IsUnit (m : R) := by
      by_contra h
      apply hm
      rw [← map_natCast (residue R), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
      exact h
    have hmK : (m : K) ≠ 0 := by
      rw [← map_natCast (algebraMap R K)]
      exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hunit.ne_zero
    refine ⟨?_, ?_⟩
    · have h' := hunit.map f
      rw [map_natCast] at h'
      rw [← map_natCast (residue _), ne_eq, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact h'
    · rw [card_torsion_fixedField (inertia K V) A hloc m (fun σ hσ x hx => hu σ hσ x hx)]
      exact GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA g hg m hmK

end UpperTheory.Lit.Nos.C6
