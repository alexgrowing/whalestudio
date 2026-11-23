import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveGoodReductionModel
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_curve_good_reduction_model : GlobalTheory.Published.SerreTateGoodReductionSt →
  ∀ (d : ℕ) (Λ : PeriodPair), d.Prime → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (k₁ : IntermediateField ℚ ℂ) (R₁ : Subring ℂ), FiniteDimensional ℚ k₁ ∧ IsPlaceOver l lam k₁ R₁ ∧ (∀ x ∈ R₁, x ∈ k₁) ∧
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧
        u.IsDiff (fun _ ↦ t) v' ∧ t ≠ 0 ∧ Sz l lam 0 ((t * Ω)⁻¹) := by
  first | exact @GlobalTheory.CMPlaceCurve.exists_curve | exact GlobalTheory.CMPlaceCurve.exists_curve | (intros; apply GlobalTheory.CMPlaceCurve.exists_curve <;> assumption)
