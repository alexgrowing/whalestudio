import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackChainCompat
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullByCompAlt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_pullback_chain_compat : ∀ (R₀ R : Subring ℂ) (ic : R₀ →+* R), (∀ x, ((ic x : R) : ℂ) = x) →
  ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A]
    (g : G.left ⟶ G₀.left) (p : A.left ⟶ G.left), IsGrpPullback G G₀ (spMap ic) g → IsGrpPullback A G (spMap R.subtype) p →
    ∀ (v₀ : epsR R₀ ⟶ G₀) (v' : epsR ℂ ⟶ A), IsTangent v₀ →
      v'.left ≫ p ≫ g = spMap (Chart.dualMapR R₀.subtype) ≫ v₀.left →
      ∃ v : epsR R ⟶ G, IsTangent v ∧ v'.left ≫ p = spMap (Chart.dualMapR R.subtype) ≫ v.left := by
  first | exact @GlobalTheory.TangentBaseChange.exists_tangent_baseChange | exact GlobalTheory.TangentBaseChange.exists_tangent_baseChange | (intros; apply GlobalTheory.TangentBaseChange.exists_tangent_baseChange <;> assumption)
