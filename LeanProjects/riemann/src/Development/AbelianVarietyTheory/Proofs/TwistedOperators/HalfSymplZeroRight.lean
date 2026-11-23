import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

variable {D : D7}

def halfPair (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) : AE D :=
  ∑ i, ∑ j, ∑ k, cA D (a k j) * incA D (W.gram k i) * t i j

def halfSympl (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * halfPair W a t)

theorem halfSympl_add_right (W : HSp D) {r : ℕ} (a t t' : Mx D W.rank r) :
    halfSympl W a (t + t') = halfSympl W a t + halfSympl W a t' := by
  simp only [halfSympl, halfPair]
  rw [← map_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_add]

theorem halfSympl_add_left (W : HSp D) {r : ℕ} (a a' t : Mx D W.rank r) :
    halfSympl W (a + a') t = halfSympl W a t + halfSympl W a' t := by
  simp only [halfSympl, halfPair]
  rw [← map_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [add_mul]

theorem halfSympl_zero_right (W : HSp D) {r : ℕ} (a : Mx D W.rank r) : halfSympl W a 0 = 0 := by
  simp [halfSympl, halfPair]

theorem halfSympl_zero_left (W : HSp D) {r : ℕ} (t : Mx D W.rank r) : halfSympl W 0 t = 0 := by
  simp [halfSympl, halfPair]

end GlobalTheory.HalfAverage
