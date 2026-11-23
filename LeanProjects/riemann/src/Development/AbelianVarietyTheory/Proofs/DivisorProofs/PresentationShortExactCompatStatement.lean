import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationShortExactCompat
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.presentation_short_exact_compat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (P₁ P₂ P₃ : Pres B) (a : P₁.E ⟶ P₂.E) (b : P₂.E ⟶ P₃.E) (a' : P₁.E' ⟶ P₂.E') (b' : P₂.E' ⟶ P₃.E') (h : a ≫ b = 0) (h' : a' ≫ b' = 0), (ShortComplex.mk a b h).ShortExact → (ShortComplex.mk a' b' h').ShortExact → P₁.ψ ≫ a = a' ≫ P₂.ψ → P₂.ψ ≫ b = b' ≫ P₃.ψ → ∀ k : ℕ, P₂.ck p k = P₁.ck p k + P₃.ck p k := by
  first | exact @GlobalTheory.MixedLocalChains.Pres.ck_add_of_shortExact | exact GlobalTheory.MixedLocalChains.Pres.ck_add_of_shortExact | (intros; apply GlobalTheory.MixedLocalChains.Pres.ck_add_of_shortExact <;> assumption)
