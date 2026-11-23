import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCorrespondenceDifferentials
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_correspondence_differentials : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E) (𝔠 : FracId (FR E))
    (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left) (U : Unif φ L 0 X)
    (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ),
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom) →
    ∃ (δ₀ : X₀.DetGen) (δ : X.DetGen) (C : ℂ), Obj.DetCorr (algebraMap Qb ℂ) p δ₀.1 δ.1 ∧ U.IsDet δ.1 C ∧
      IsAlgebraic ℚ (C * ∏ i, a i) := by
  first | exact @GlobalTheory.LatJet.exists_detGen_coeff_algebraic | exact GlobalTheory.LatJet.exists_detGen_coeff_algebraic | (intros; apply GlobalTheory.LatJet.exists_detGen_coeff_algebraic <;> assumption)
