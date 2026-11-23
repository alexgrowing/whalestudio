import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsomorphismSubbundleLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_isomorphism_subbundle_lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (r : ℕ) (E E' : B.X.Modules) (φ : B.GenIso E E'), GlobalTheory.VB.IsVB E (r + 1) → GlobalTheory.VB.IsVB E' (r + 1) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (K K' : B'.X.Modules) (i : K ⟶ (Scheme.Modules.pullback f.f).obj E) (i' : K' ⟶ (Scheme.Modules.pullback f.f).obj E') (ψ : B'.GenIso K K'), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ GlobalTheory.VB.IsSubbundle i ∧ GlobalTheory.VB.IsSubbundle i' ∧ GlobalTheory.VB.IsVB K r ∧ GlobalTheory.VB.IsVB K' r ∧ ψ.hom ≫ B'.genRes.map i' = B'.genRes.map i ≫ (φ.pull f.comp_str).hom := by
  first | exact @GlobalTheory.CorankPair.exists_corankOne_pair | exact GlobalTheory.CorankPair.exists_corankOne_pair | (intros; apply GlobalTheory.CorankPair.exists_corankOne_pair <;> assumption)
