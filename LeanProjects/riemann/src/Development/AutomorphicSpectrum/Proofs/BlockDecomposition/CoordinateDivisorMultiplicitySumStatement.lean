import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateDivisorMultiplicitySum
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
theorem _root_.GlobalTheory.T.coordinate_divisor_multiplicity_sum : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (k : Fin (m + 1)) (l : Bk n k) (hs : genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l))) (u : Ideal (Pol n) → ℤ), ∑ᶠ w, (divOfSec (isLB_pullO (f ≫ prB n k) 1) (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) hs).mult w * u (ptIdeal (f w)) = ∑ᶠ W ∈ divSupp (ptIdeal (f (genericPoint Z))) (X ⟨k, l⟩ : Pol n), (multAt (ptIdeal (f (genericPoint Z)) ⊔ Ideal.span {(X ⟨k, l⟩ : Pol n)}) W : ℤ) * u W := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.DivCyc.divOfSec_cycle | exact GlobalTheory.CompanionTheory.MixZ.DivCyc.divOfSec_cycle | (intros; apply GlobalTheory.CompanionTheory.MixZ.DivCyc.divOfSec_cycle <;> assumption)
