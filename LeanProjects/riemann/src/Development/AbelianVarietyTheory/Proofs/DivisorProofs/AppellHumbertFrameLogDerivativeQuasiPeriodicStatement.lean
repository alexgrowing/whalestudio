import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFrameLogDerivativeQuasiPeriodic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_frame_log_derivative_quasi_periodic : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → L.IsLB → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.IsAH H χ → ∀ v : Fin g → ℂ, (∀ i, DifferentiableOn ℂ (fun z => fderiv ℂ (u.fr i) z v / u.fr i z) (pre u.ex (L.U i))) ∧ (∀ i j, IsReg u.ex (L.U i ⊓ L.U j) ((fun z => fderiv ℂ (u.fr i) z v / u.fr i z) - fun z => fderiv ℂ (u.fr j) z v / u.fr j z)) ∧ ∀ i (l : u.Λ), ∀ z ∈ pre u.ex (L.U i), fderiv ℂ (u.fr i) (z + l) v / u.fr i (z + l) = fderiv ℂ (u.fr i) z v / u.fr i z - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  first | exact @GlobalTheory.CechPer.LogDer.main | exact GlobalTheory.CechPer.LogDer.main | (intros; apply GlobalTheory.CechPer.LogDer.main <;> assumption)
