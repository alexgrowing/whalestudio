import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMapExtendsAfterScaling
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_map_extends_after_scaling : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : GlobalTheory.Vert.Model O)
    (E E' : Z.X.Modules) (n m : ℕ), GlobalTheory.VB.IsVB E n → GlobalTheory.VB.IsVB E' m → ∀ (a : Z.genRes.obj E ⟶ Z.genRes.obj E'),
    ∃ (g : O) (u : E ⟶ E'), g ≠ 0 ∧ Z.genRes.map u = a ≫ Z.genRes.map (smulHom E' (Z.const g)) := by
  first | exact @GlobalTheory.ClearDenom.exists_smul_eq_genRes_map | exact GlobalTheory.ClearDenom.exists_smul_eq_genRes_map | (intros; apply GlobalTheory.ClearDenom.exists_smul_eq_genRes_map <;> assumption)
