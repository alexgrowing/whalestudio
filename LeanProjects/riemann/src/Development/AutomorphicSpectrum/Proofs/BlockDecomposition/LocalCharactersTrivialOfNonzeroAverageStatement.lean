import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharactersTrivialOfNonzeroAverage
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTrivialOfNonzeroSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationVectorHomomorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNormOneUnitsTrivialValuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedStandardValuesAtIntegralStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_characters_trivial_of_nonzero_average : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K)
  (M : ∀ v : Pl, LM c v), AdmM M → ∀ R : Finset (Pl →₀ ℤ), IsReps M R → ∀ Sv : Finset Pl, GoodSv M Sv →
  (∀ κ ∈ K1 K, ∏ᶠ v, (M v).ct (k1 (M v) κ) = 1) → (∑ m ∈ R, ∫ u, ctM M Sv m u ∂muU Sv) ≠ 0 →
  ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1 := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.Orth.weights_trivial | exact GlobalTheory.CompanionTheory.FexTheta.Orth.weights_trivial | (intros; apply GlobalTheory.CompanionTheory.FexTheta.Orth.weights_trivial <;> assumption)
