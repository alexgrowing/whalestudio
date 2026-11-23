import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericIsosSubbundleModification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_isos_subbundle_modification : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (r : ℕ) (E E' E'' : B.X.Modules) (φ : B.GenIso E E') (φ' : B.GenIso E' E''), GlobalTheory.VB.IsVB E (r + 1) → GlobalTheory.VB.IsVB E' (r + 1) → GlobalTheory.VB.IsVB E'' (r + 1) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (K K' K'' : B'.X.Modules) (i : K ⟶ (Scheme.Modules.pullback f.f).obj E) (i' : K' ⟶ (Scheme.Modules.pullback f.f).obj E') (i'' : K'' ⟶ (Scheme.Modules.pullback f.f).obj E'') (ψ : B'.GenIso K K') (ψ' : B'.GenIso K' K''), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ GlobalTheory.VB.IsSubbundle i ∧ GlobalTheory.VB.IsSubbundle i' ∧ GlobalTheory.VB.IsSubbundle i'' ∧ GlobalTheory.VB.IsVB K r ∧ GlobalTheory.VB.IsVB K' r ∧ GlobalTheory.VB.IsVB K'' r ∧ ψ.hom ≫ B'.genRes.map i' = B'.genRes.map i ≫ (φ.pull f.comp_str).hom ∧ ψ'.hom ≫ B'.genRes.map i'' = B'.genRes.map i' ≫ (φ'.pull f.comp_str).hom := by
  first | exact @GlobalTheory.CorankTriple.exists_corankOne_triple | exact GlobalTheory.CorankTriple.exists_corankOne_triple | (intros; apply GlobalTheory.CorankTriple.exists_corankOne_triple <;> assumption)
