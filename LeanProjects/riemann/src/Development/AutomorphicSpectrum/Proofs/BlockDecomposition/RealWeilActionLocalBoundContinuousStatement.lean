import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionLocalBoundContinuous
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_weil_action_local_bound_continuous : ∀ (n : ℤ) (t : ℝ) (g₀ : GL (Fin 2) ℝ), 0 < (g₀.val).det → ∃ W ∈ nhds g₀, ∃ A : ℝ,
  (∀ g ∈ W, ∀ x : ℂ, ‖piRc (chC n (Complex.I * t)) g (PhiInf n) x‖ ≤ A * ((1 + ‖x‖) ^ 4)⁻¹) ∧
  ∀ x : ℂ, ContinuousAt (fun g => piRc (chC n (Complex.I * t)) g (PhiInf n) x) g₀ := by
  first | exact @GlobalTheory.CompanionTheory.ArchDecay.piRc_decay | exact GlobalTheory.CompanionTheory.ArchDecay.piRc_decay | (intros; apply GlobalTheory.CompanionTheory.ArchDecay.piRc_decay <;> assumption)
