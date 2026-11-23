import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubspaceMapExtends
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
theorem _root_.GlobalTheory.T.generic_subspace_map_extends : ∀ (X : Scheme.{0}) [IsIntegral X] (F G : X.Modules) (u : F ⟶ G)
    (N : Submodule X.functionField (GlobalTheory.VB.genStalk F)) (N' : Submodule X.functionField (GlobalTheory.VB.genStalk G)),
    (∀ t ∈ N, GlobalTheory.QCoh.stalkLinear u (genericPoint X) t ∈ N') →
    ∃ v : (GlobalTheory.VB.Sub.ofGeneric N).toMod ⟶ (GlobalTheory.VB.Sub.ofGeneric N').toMod,
      v ≫ (GlobalTheory.VB.Sub.ofGeneric N').incl = (GlobalTheory.VB.Sub.ofGeneric N).incl ≫ u := by
  first | exact @GlobalTheory.VB.exists_ofGeneric_hom_of_mapsTo | exact GlobalTheory.VB.exists_ofGeneric_hom_of_mapsTo | (intros; apply GlobalTheory.VB.exists_ofGeneric_hom_of_mapsTo <;> assumption)
