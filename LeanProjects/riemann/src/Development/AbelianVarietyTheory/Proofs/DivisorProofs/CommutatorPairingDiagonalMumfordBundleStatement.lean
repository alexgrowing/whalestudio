import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDiagonalMumfordBundle
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutator_pairing_diagonal_mumford_bundle : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (N : LB A.left), N.IsLB → LBIso N (cubeLB A ![𝟙 A, 𝟙 A] M) → Out.RelAmple A N → ∀ (k : ℕ) (a b : Fin g → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm a b).im : ℝ)) : ℂ) / k) → Out.WeilIs A N k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  first | exact @GlobalTheory.DiagWeil.weilIs_diag_lam | exact GlobalTheory.DiagWeil.weilIs_diag_lam | (intros; apply GlobalTheory.DiagWeil.weilIs_diag_lam <;> assumption)
