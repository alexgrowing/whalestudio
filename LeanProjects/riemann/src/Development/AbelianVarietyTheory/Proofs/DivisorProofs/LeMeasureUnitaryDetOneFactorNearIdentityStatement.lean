import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMeasureUnitaryDetOneFactorNearIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_measure_unitaryDetOneFactor_near_identity : ∀ (p q : ℕ) (a₀ : Fin p ⊕ Fin q) (m : Measure (UpqT p q)), IsMinf m → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ENNReal.ofReal (ε ^ ((p + q) ^ 2 - 1) / ((p + q : ℕ) : ℝ) ^ (p + q - 1)) ≤ m {u | (∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε) ∧ 0 < (UpqT.mat u).det.im} := by
  first | exact @GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near | exact GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near | (intros; apply GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near <;> assumption)
