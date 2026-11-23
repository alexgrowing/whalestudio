import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumOverCosetRepresentatives
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
theorem _root_.GlobalTheory.T.hasSum_over_coset_representatives : ∀ {H A : Type} [CommGroup H] [AddCommGroup A] (T : AddSubgroup A) (φ : H → A), (∀ h, φ h ∈ T) →
  (∀ a b, φ (a * b) = φ a + φ b) → ∀ R : Finset A, (∀ r ∈ R, r ∈ T) →
  (∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ h, m = r + φ h) → Finite {h : H // φ h = 0} →
  ∀ (F : A → ℂ) (s : ℂ), HasSum (fun m : T => F m) s →
    HasSum (fun h : H => ∑ r ∈ R, F (r + φ h)) ((Nat.card {h : H // φ h = 0} : ℂ) * s) := by
  first | exact @GlobalTheory.CompanionTheory.OrbitSums.orbit_sum_unfold | exact GlobalTheory.CompanionTheory.OrbitSums.orbit_sum_unfold | (intros; apply GlobalTheory.CompanionTheory.OrbitSums.orbit_sum_unfold <;> assumption)
