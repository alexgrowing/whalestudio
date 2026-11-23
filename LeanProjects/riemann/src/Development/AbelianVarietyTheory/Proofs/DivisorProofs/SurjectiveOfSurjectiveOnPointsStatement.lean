import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfSurjectiveOnPoints
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_surjective_on_points : ∀ (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (ψ : A ⟶ X), IsAbelianScheme A → IsAbelianScheme X →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) → Surjective ψ.left := by
  first | exact @GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points | exact GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points | (intros; apply GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points <;> assumption)
