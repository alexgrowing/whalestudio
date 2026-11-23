import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergEqLFactor
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.CauchyVariationInequality
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_rankin_selberg_eq_L_factor : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (W : GL (Fin 3) F → ℂ) (W' : GL (Fin 2) F → ℂ) (S S' : ℤ → ℤ → ℂ) (s R : ℂ), (∀ a b : ℤ, W (dg (unifUnit F ^ a) (unifUnit F ^ b) 1) = if b ≤ a ∧ 0 ≤ b then (residueCard F : ℂ) ^ (-a) * S a b else 0) → (∀ a b : ℤ, W' (d2 (unifUnit F ^ a) (unifUnit F ^ b)) = if b ≤ a then Spherical.sqrtQ F ^ (-(a - b)) * S' a b else 0) → HasSum (fun p : ℕ × ℕ => S ((p.1 + p.2 : ℕ) : ℤ) (p.2 : ℤ) * S' ((p.1 + p.2 : ℕ) : ℤ) (p.2 : ℤ) * ((residueCard F : ℂ) ^ (-s)) ^ (p.1 + 2 * p.2)) R → zU W W' s = R := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.ZUSum.zU_eq_of_hasSum | exact GlobalTheory.CompanionTheory.GL2Factorization.ZUSum.zU_eq_of_hasSum | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.ZUSum.zU_eq_of_hasSum <;> assumption)
