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

namespace GlobalTheory.VB

theorem exists_ofGeneric_hom_of_mapsTo :
    ∀ (X : Scheme.{0}) [IsIntegral X] (F G : X.Modules) (u : F ⟶ G)
    (N : Submodule X.functionField (GlobalTheory.VB.genStalk F)) (N' : Submodule X.functionField (GlobalTheory.VB.genStalk G)),
    (∀ t ∈ N, GlobalTheory.QCoh.stalkLinear u (genericPoint X) t ∈ N') →
    ∃ v : (GlobalTheory.VB.Sub.ofGeneric N).toMod ⟶ (GlobalTheory.VB.Sub.ofGeneric N').toMod,
      v ≫ (GlobalTheory.VB.Sub.ofGeneric N').incl = (GlobalTheory.VB.Sub.ofGeneric N).incl ≫ u := by
  intro X _ F G u N N' h
  refine ((GlobalTheory.VB.Sub.ofGeneric N').exists_comp_incl_iff _).2 fun V s hV => ?_
  have := h _ ((GlobalTheory.VB.Sub.ofGeneric N).incl_app_mem s hV)
  rw [GlobalTheory.QCoh.stalkLinear_germ] at this
  exact this

end GlobalTheory.VB
