import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricSmoothPshIffPotentialPsh
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_smooth_psh_iff_potential_psh : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y), e = Y.dim → ∀ (Δ : Y.Dv) (a : Fin (M.n + 1)) (m : (cxSt F).Met Y (I.ε a) Δ) (Q : LocPot (M.X a)), IsPot (I.pt a) m Q → IsPotential (M.A a) Q → (cxSt F).mSmooth Y (I.ε a) Δ m ∧ ((cxSt F).mPsh Y (I.ε a) Δ m 0 ↔ IsPsh (M.A a) Q) := by
  first | exact @GlobalTheory.PotSmoothPsh.smooth_and_mPsh_iff | exact GlobalTheory.PotSmoothPsh.smooth_and_mPsh_iff | (intros; apply GlobalTheory.PotSmoothPsh.smooth_and_mPsh_iff <;> assumption)
