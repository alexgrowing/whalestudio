import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureDetOneFactorNearIdentityLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_detOneFactor_nearIdentity_le : ∀ (p q : ℕ) (a₀ : Fin p ⊕ Fin q) (m : Measure (UpqT p q)), IsMinf m → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → m {u | ∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε} ≤ ENNReal.ofReal ((200 * ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * ε ^ ((p + q) ^ 2 - 1)) := by
  first | exact @GlobalTheory.CovTop.VolUp.OneMeasure.measure_sMat_near_le | exact GlobalTheory.CovTop.VolUp.OneMeasure.measure_sMat_near_le | (intros; apply GlobalTheory.CovTop.VolUp.OneMeasure.measure_sMat_near_le <;> assumption)
