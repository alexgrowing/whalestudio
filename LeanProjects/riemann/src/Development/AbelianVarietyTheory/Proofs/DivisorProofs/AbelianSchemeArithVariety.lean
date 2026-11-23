import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

namespace GlobalTheory.PPAS

theorem isArithVar_total : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p →
    ∀ (P : PPAS S), IsArithVar (P.A.hom ≫ p) (P.g + 1) := by
  intro k _ S p hS P
  have hV := hS.toIsArithVar
  have := hV.isIntegral
  have := hV.finite
  have := hV.isLocallyNoetherian
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have hI : IsIntegral P.A.left := isIntegral_of_smooth_of_geometricallyConnected P.A.hom
  have hsurj : Function.Surjective P.A.hom := Surjective.surj
  have hdS : topologicalKrullDim S = ((1 : ℕ) + 1 : ℕ) := hV.dim_eq
  have hdA := GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective S P.A.left P.A.hom
    P.g 1 hsurj hdS
  refine RegCoverExists.isArithVar_of_toSpZ hV.isDomain hV.finite _ (s := ShFam.Pad.toSpZ P.A.left)
    ⟨inferInstance, inferInstance, hI,
      isProjOver_of_isProjOver_base S P (ShFam.Pad.isProjOver_toSpZ hV.isProjOver), ?_, ?_⟩
  · rw [specZIsTerminal.hom_ext (ShFam.Pad.toSpZ P.A.left ≫ spMap (Int.castRingHom ℤ))
      (P.A.hom ≫ p ≫ spMap (Int.castRingHom k))]
    have := hV.flat
    infer_instance
  · rw [hdA]; congr 2; omega

end GlobalTheory.PPAS
