import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiAStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem finiteDimensional_of_finite_of_isFractionRing (V K W L : Type) [CommRing V] [IsDomain V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [Field L] [Algebra V W] [Algebra W L] [Algebra K L]
    [IsFractionRing W L] [Module.Finite V W]
    (e : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K)) :
    FiniteDimensional K L := by
  letI : Algebra V L := ((algebraMap W L).comp (algebraMap V W)).toAlgebra
  haveI : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' e
  haveI : FaithfulSMul V W := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h : Function.Injective ((algebraMap W L).comp (algebraMap V W)) := by
      rw [e]; exact (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    exact Function.Injective.of_comp (f := algebraMap W L) h
  exact Module.Finite.of_isLocalization V W (nonZeroDivisors V)

theorem exists_ringHom_integralClosure (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W L : Type) [CommRing W] [IsDomain W] [Field L]
    [Algebra (integralClosure ℤ_[p] K) W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    [Module.Finite (integralClosure ℤ_[p] K) W]
    (e : (algebraMap W L).comp (algebraMap (integralClosure ℤ_[p] K) W) =
      (algebraMap K L).comp (algebraMap (integralClosure ℤ_[p] K) K)) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (τ : L →+* K') (f : W →+* integralClosure ℤ_[p] K'),
        τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom ∧
        τ.comp (algebraMap W L) = (algebraMap (integralClosure ℤ_[p] K') K').comp f := by
  haveI := finiteDimensional_of_finite_of_isFractionRing _ K W L e
  let σ : L →ₐ[K] PadicAlgCl p := IsAlgClosed.lift
  let K' : IntermediateField ℚ_[p] (PadicAlgCl p) := σ.fieldRange.restrictScalars ℚ_[p]
  have h : K ≤ K' := fun x hx => ⟨algebraMap K L ⟨x, hx⟩, σ.commutes _⟩
  let τ : L →+* K' := σ.toRingHom.codRestrict K' fun x => ⟨x, rfl⟩
  have hτ : τ.comp (algebraMap K L) = (IntermediateField.inclusion h).toRingHom :=
    RingHom.ext fun x => Subtype.ext (σ.commutes x)
  have hK' : FiniteDimensional ℚ_[p] K' := by
    letI : Algebra ℚ_[p] L := ((algebraMap K L).comp (algebraMap ℚ_[p] K)).toAlgebra
    haveI : IsScalarTower ℚ_[p] K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℚ_[p] L := Module.Finite.trans K L
    let τ' : L →ₐ[ℚ_[p]] K' := { τ with commutes' := fun x => Subtype.ext (σ.commutes (algebraMap ℚ_[p] K x)) }
    refine Module.Finite.of_surjective τ'.toLinearMap ?_
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hint : ∀ w : W, IsIntegral ℤ_[p] (τ (algebraMap W L w)) := fun w => by
    have h₁ : (algebraMap (integralClosure ℤ_[p] K) W).IsIntegralElem w := Algebra.IsIntegral.isIntegral w
    letI : Algebra (integralClosure ℤ_[p] K) K' :=
      ((IntermediateField.inclusion h).toRingHom.comp (algebraMap (integralClosure ℤ_[p] K) K)).toAlgebra
    haveI : IsScalarTower ℤ_[p] (integralClosure ℤ_[p] K) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h₂ := h₁.map (τ.comp (algebraMap W L))
    rw [RingHom.comp_assoc, e, ← RingHom.comp_assoc, hτ] at h₂
    exact isIntegral_trans (A := integralClosure ℤ_[p] K) _ h₂
  exact ⟨K', h, hK', τ, (τ.comp (algebraMap W L)).codRestrict _ hint, hτ, RingHom.ext fun _ => rfl⟩

theorem exists_semiAbelian_model_padic_polAV : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (P : Out.PolAV (Sp K)), ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧ ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧ ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left, IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  intro p _ K _ P
  haveI := GlobalTheory.DiscEval.isAdicComplete_integralClosure K
  obtain ⟨W, L, _, _, _, _, _, _, _, _, e, hfin, -, -, G, _, ⟨i, hi⟩, hG⟩ :=
    GlobalTheory.T.principallyPolarizedAbelianVariety_potentialSemiAbelianModel (integralClosure ℤ_[p] K) K (GlobalTheory.DiscEval.finite_residueField_integralClosure K) P
  obtain ⟨K', h, hK', τ, f, hτ, hf⟩ := exists_ringHom_integralClosure p K W L e
  refine ⟨K', h, hK', (Over.pullback (spMap f)).obj G, inferInstance, IsSemiAbelian.pullback _ G hG, ?_⟩
  exact GlobalTheory.SplitReduction.exists_isGrpPullback_of_square hf hτ G P.A
    (((isGrpPullback_of_iso i).comp (isGrpPullback_pullback P.A (spMap (algebraMap K L)))).congr
      (Category.id_comp _) rfl)

end GlobalTheory.SS
