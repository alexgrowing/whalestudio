import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

namespace GlobalTheory.DbarChain

theorem d01_comp_holomorphic {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (φ : E' → E) (H : E → ℂ) (b v : E')
    (hφ : DifferentiableAt ℂ φ b) (hH : DifferentiableAt ℝ H (φ b)) :
    d01 (fun c => H (φ c)) b v = d01 H (φ b) (fderiv ℂ φ b v) := by
  have hφR : DifferentiableAt ℝ φ b := hφ.restrictScalars ℝ
  have hcomp : fderiv ℝ (fun c => H (φ c)) b = (fderiv ℝ H (φ b)).comp (fderiv ℝ φ b) :=
    fderiv_comp (x := b) (g := H) (f := φ) hH hφR
  have hres : fderiv ℝ φ b = (fderiv ℂ φ b).restrictScalars ℝ := hφ.fderiv_restrictScalars ℝ
  unfold d01
  rw [hcomp, hres]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

end GlobalTheory.DbarChain
