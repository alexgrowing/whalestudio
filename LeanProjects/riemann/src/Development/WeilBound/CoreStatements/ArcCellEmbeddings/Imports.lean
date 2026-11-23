import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ZeroMemLieBall
open MeasureTheory Filter Topology Matrix Metric Set GlobalTheory.SUVol GlobalTheory.CompanionTheory.Ar.abelian₂
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace UnitaryFrameBall.Tr

variable {ι : Type} {r : ℕ}

def trB [Fintype ι] (H : ι → Matrix (Fin r) (Fin r) ℂ) : LinearMap.BilinForm ℝ (suLie H) :=
  LinearMap.mk₂ ℝ (fun X Y => trForm X.1 Y.1)
    (fun X X' Y => by simp [trForm, Matrix.add_mul, Finset.sum_add_distrib])
    (fun c X Y => by simp [trForm, Finset.mul_sum])
    (fun X Y Y' => by simp [trForm, Matrix.mul_add, Finset.sum_add_distrib])
    (fun c X Y => by simp [trForm, Finset.mul_sum])

theorem gram_eq [Fintype ι] {H : ι → Matrix (Fin r) (Fin r) ℂ} {n : ℕ} (b : Module.Basis (Fin n) ℝ (suLie H)) :
    (Matrix.of fun k l => trForm (b k).1 (b l).1) = LinearMap.BilinForm.toMatrix b (trB H) := by
  ext k l
  rw [LinearMap.BilinForm.toMatrix_apply]
  rfl

end UnitaryFrameBall.Tr
