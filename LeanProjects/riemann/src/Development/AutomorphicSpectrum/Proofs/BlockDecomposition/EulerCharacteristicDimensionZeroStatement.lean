import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharacteristicDimensionZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_characteristic_dimension_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = (0 : ℕ) → ∀ a : Fin 0 → Fin (m + 1) → ℤ, chi (ZMod p) (structureModule Z) = geoNum 0 (ptIdeal (f (genericPoint Z))) a := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.VertBase.chi_eq_geoNum | exact GlobalTheory.CompanionTheory.MixZ.VertBase.chi_eq_geoNum | (intros; apply GlobalTheory.CompanionTheory.MixZ.VertBase.chi_eq_geoNum <;> assumption)
