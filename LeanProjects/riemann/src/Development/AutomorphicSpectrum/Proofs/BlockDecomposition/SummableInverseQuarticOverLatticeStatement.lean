import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableInverseQuarticOverLattice
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_inverse_quartic_over_lattice : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ N : ℕ, N ≠ 0 →
  Summable (fun ξ : {ξ : K // ∃ a : 𝓞 K, (N : K) * ξ = a} => ((1 + ‖embC K ξ.1‖) ^ 4)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.LatticeSum.summable_inv_one_add_norm_pow_four | exact GlobalTheory.CompanionTheory.LatticeSum.summable_inv_one_add_norm_pow_four | (intros; apply GlobalTheory.CompanionTheory.LatticeSum.summable_inv_one_add_norm_pow_four <;> assumption)
