import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianVarietyDescendsOfRationalThetaPoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisBaseChangeStatement
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypSOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreThetaConstantsAlgebraicOverCompleteAlgCloseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GeoDesc

theorem exists_geomIso_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) ∧ (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) ∧ GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) := by
  intro R _ _ _ hR D n hn ho hu W _ _ _ hW φ hφ hloc D' G' _ _ A' hD hG hU hS
  haveI : CharZero R := hR.2
  haveI : CharZero (Kb R) := charZero_of_injective_ringHom (f := (algebraMap (FractionRing R) (Kb R)).comp
    (algebraMap R (FractionRing R))) ((algebraMap (FractionRing R) (Kb R)).injective.comp
      (IsFractionRing.injective R (FractionRing R)))
  let φK : FractionRing R →+* FractionRing W :=
    IsFractionRing.lift (g := (algebraMap W (FractionRing W)).comp φ) ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp φK).toAlgebra
  haveI : Module.IsTorsionFree (FractionRing R) (Kb W) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (FractionRing R) (Kb R) := DivisionSemiring.to_moduleIsTorsionFree
  let e₀ : Kb R →+* Kb W := (IsAlgClosed.lift : Kb R →ₐ[FractionRing R] Kb W).toRingHom
  have he₀ : ∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) =
      algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r)) := by
    intro r
    show (IsAlgClosed.lift : Kb R →ₐ[FractionRing R] Kb W) (algebraMap _ _ _) = _
    rw [AlgHom.commutes]
    show algebraMap (FractionRing W) (Kb W) (φK _) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  obtain ⟨B, b, hB⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds (algebraMap (FractionRing W) (Kb W)) A'
  have hth : ∀ j : ℕ, 1 ≤ j → ∃ (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R),
      (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧
      IsThetaPt B (n ^ j) x fun i => (Scheme.ΓSpecIso (CommRingCat.of (Kb W))).inv.hom (e₀ (v i)) := by
    intro j hj
    obtain ⟨C, _, jC, Ix, x, v, hcov, htor, hC⟩ :=
      GlobalTheory.T.fibre_thetaConstants_algebraic_over_completeAlgClosed R hR D n hn ho hu W hW φ hφ hloc D' G' A' hD hG hU e₀ he₀ B b hB.2.1 hB.2.2.symm j hj
    exact ⟨Ix, x, v, hcov, GlobalTheory.Mum.ThetaDown.isThetaPt_of_map (Sp (Kb W)) B (Kb W) C jC (𝟙 _) (spMap jC) (Category.comp_id _) (n ^ j) Ix x
      (fun i => e₀ (v i)) htor hC⟩
  obtain ⟨A₀, a, ha, hLa⟩ := GlobalTheory.T.polarisedAbelianVariety_descends_of_rational_thetaPoints (Kb R) (Kb W) e₀ B n hn ho hth
  refine ⟨A₀, e₀, he₀, ?_, B, a, b, ha, hLa, hB.2.1, hB.2.2.symm⟩
  exact GlobalTheory.SymDescentAlgClosed.hypS_of_baseChange (Kb R) (Kb W) e₀ A₀ B a ha hLa (GlobalTheory.T.lineBundleSymmetryHypothesis_baseChange _ _ _ A' B b hB hS)

end GlobalTheory.Mum.GeoDesc
