import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentWithUniformization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_descent_with_uniformization : ∀ (k : Type) [Field k] (σ : k →+* ℂ) (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A]
    (p : A.left ⟶ A₀.left) (L : LB A.left) (u : HolUnif A L 1), IsAbelianScheme A₀ → SmoothOfRelativeDimension 1 A₀.hom →
    IsGrpPullback A A₀ (spMap σ) p → L.IsLB → ∀ n : ℕ,
  ∃ (B₀ : Over (Sp k)) (_ : GrpObj B₀) (B : Over (Sp ℂ)) (_ : GrpObj B) (q : B.left ⟶ B₀.left) (M : LB B.left)
    (v : HolUnif B M n), IsAbelianScheme B₀ ∧ SmoothOfRelativeDimension n B₀.hom ∧ IsAbelianScheme B ∧
    SmoothOfRelativeDimension n B.hom ∧ IsGrpPullback B B₀ (spMap σ) q ∧ ∀ z ∈ v.Λ, ∀ j, (fun _ : Fin 1 ↦ z j) ∈ u.Λ := by
  first | exact @GlobalTheory.EllPowModel.main | exact GlobalTheory.EllPowModel.main | (intros; apply GlobalTheory.EllPowModel.main <;> assumption)
