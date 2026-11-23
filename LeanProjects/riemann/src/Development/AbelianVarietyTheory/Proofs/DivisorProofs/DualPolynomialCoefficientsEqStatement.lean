import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPolynomialCoefficientsEq
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_polynomial_coefficients_eq : ∀ (q r : ℕ) (f : ℂ[X]) (a w : ℕ → ℂ), q ≠ 0 → f.coeff 0 = 1 → f.natDegree ≤ r → (∀ k, a k = (f.map (starRingEnd ℂ)).coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))) → (∀ k, w k = (dualPoly ((q : ℂ) ^ (r - 1)) f).coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))) → ((a r ≠ 0 ∧ ∀ k ≤ r, star (a k) * a r = a (r - k)) ∨ (w r ≠ 0 ∧ ∀ k ≤ r, star (w k) * w r = w (r - k))) → ∀ k ≤ r, a k = w k := by
  first | exact @GlobalTheory.PolUnitary.conj_eq_dual | exact GlobalTheory.PolUnitary.conj_eq_dual | (intros; apply GlobalTheory.PolUnitary.conj_eq_dual <;> assumption)
