import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaZeroTermUnipotentInvariant
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_zero_term_unipotent_invariant : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ)
  (M : ∀ v : Pl, LM c v), AdmM M → ∀ (x : 𝔸[ℚ]) (g : G2), thT n t M (uni2 x * g) 0 = thT n t M g 0 := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.ZeroTerm.theta_zero_term_unipotent_invariant_adelic | exact GlobalTheory.CompanionTheory.FexTheta.ZeroTerm.theta_zero_term_unipotent_invariant_adelic | (intros; apply GlobalTheory.CompanionTheory.FexTheta.ZeroTerm.theta_zero_term_unipotent_invariant_adelic <;> assumption)
