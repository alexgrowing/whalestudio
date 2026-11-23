import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkChainPeriodicRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ck_chain_periodic_relation : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (ι : Type) (φ : ι → ι) (o : ℕ) (Ch : Chain p B φ o), (∀ τ, φ^[o] τ = τ) → ∀ (k : ℕ) (La : ι → PicSym B.X →ₗ[ℚ] ℚ), (∀ τ, La τ = ckP p (GlobalTheory.Vert.Model.GenIso.smul (Ch.lw τ).E' (p : O) (GlobalTheory.Vert.natCast_ne_zero O p)) (Ch.lw τ).r k) → ∀ τ, (1 - ((p : ℚ) ^ (o * k))⁻¹) • ((Ch.oo τ).ck p k - (Ch.lw τ).ck p k + ((p : ℚ) - 1)⁻¹ • La τ) = ∑ n ∈ Finset.range o, ((p : ℚ) ^ ((n + 1) * k))⁻¹ • La (φ^[n + 1] τ) := by
  first | exact @GlobalTheory.MixedLocalChains.Chain.ck_period | exact GlobalTheory.MixedLocalChains.Chain.ck_period | (intros; apply GlobalTheory.MixedLocalChains.Chain.ck_period <;> assumption)
