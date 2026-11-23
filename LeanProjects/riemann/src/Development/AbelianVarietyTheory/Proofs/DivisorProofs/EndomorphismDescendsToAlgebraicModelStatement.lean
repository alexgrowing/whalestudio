import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismDescendsToAlgebraicModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_descends_to_algebraic_model : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
      ∀ (α : X.A ⟶ X.A) [IsMonHom α], ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left := by
  first | exact @GlobalTheory.RealMult.Obj.exists_end_descend_algebraic | exact GlobalTheory.RealMult.Obj.exists_end_descend_algebraic | (intros; apply GlobalTheory.RealMult.Obj.exists_end_descend_algebraic <;> assumption)
