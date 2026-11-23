import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveLatticePeriodForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_curve_lattice_period_form : ∀ (d : ℕ) (τ : ℂ), 0 < d → τ ^ 2 = -(d : ℂ) →
  ∃ (A₀ : Over (Sp Qb)) (_ : GrpObj A₀) (A : Over (Sp ℂ)) (_ : GrpObj A) (p : A.left ⟶ A₀.left) (L : LB A.left)
    (u : HolUnif A L 1) (c : ℂ), IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension 1 A₀.hom ∧
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p ∧ L.IsLB ∧ c ≠ 0 ∧ ∀ z ∈ u.Λ, ∃ a b : ℤ, z 0 = c * (a + b * τ) := by
  first | exact @GlobalTheory.CMModel.exists_curve_lattice | exact GlobalTheory.CMModel.exists_curve_lattice | (intros; apply GlobalTheory.CMModel.exists_curve_lattice <;> assumption)
