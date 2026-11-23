import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntNe
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_of_isCMType_of_ne : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i j, i ≠ j → ∃ b : 𝓞 (FR E), φ i ((b : FR E) : E) ≠ φ j ((b : FR E) : E) := by
  first | exact @GlobalTheory.CMSep.exists_int_ne' | exact GlobalTheory.CMSep.exists_int_ne' | (intros; apply GlobalTheory.CMSep.exists_int_ne' <;> assumption)
