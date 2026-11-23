import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMSep

theorem exists_int_ne' : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i j, i ≠ j → ∃ b : 𝓞 (FR E), φ i ((b : FR E) : E) ≠ φ j ((b : FR E) : E) :=
  fun {E} _ _ _ {I} φ hφ i j hij => exists_int_ne E I φ hφ i j hij

end GlobalTheory.CMSep
