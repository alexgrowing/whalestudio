import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

theorem star_trace_mat_of_unitLie {D : D7} {S T : HSp D} (C : Ctx S T) {Z : Frame C.X.Ψ T.rank}
    (hZ : Z ∈ GlobalTheory.HolRead.unitLie C.X) (σ : C.X.Ψ) : star (trace (mat Z σ)) = -trace (mat Z σ) := by
  set Sg : Matrix (Fin T.rank) (Fin T.rank) ℂ := diagonal fun a : Fin T.rank => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ) with hSg
  have hSS : Sg * Sg = 1 := by
    rw [hSg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> norm_num
  have h := hZ σ
  have h2 : Sg * ((mat Z σ)ᴴ * Sg + Sg * mat Z σ) = 0 := by rw [h, Matrix.mul_zero]
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hSS, Matrix.one_mul] at h2
  have h3 := congrArg trace h2
  rw [trace_add, trace_zero, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hSS, Matrix.mul_one,
    trace_conjTranspose] at h3
  exact eq_neg_of_add_eq_zero_left h3

theorem trace_mat_eq_zero_of_add_I {D : D7} {S T : HSp D} (C : Ctx S T) (ρ : D.what₂.Tau) (c d : Fin T.rank) (hcd : c < d)
    {Z Z' : Frame C.X.Ψ T.rank} (hZ : Z ∈ GlobalTheory.HolRead.unitLie C.X) (hZ' : Z' ∈ GlobalTheory.HolRead.unitLie C.X)
    (h : Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) (σ : C.X.Ψ) :
    trace (mat Z σ) = 0 ∧ trace (mat Z' σ) = 0 := by
  have e : mat Z σ + I • mat Z' σ = mat (GlobalTheory.HolRead.unitFr (C.m.e ρ) c d) σ := by rw [← h]; rfl
  have e0 : trace (mat Z σ) + I * trace (mat Z' σ) = 0 := by
    have := congrArg trace e
    rw [trace_add, trace_smul, smul_eq_mul, GlobalTheory.HolRead.AdExt.mat_unitFr] at this
    rw [this]
    split_ifs
    · simp [Matrix.trace, Matrix.single, hcd.ne']
    · simp
  have a := star_trace_mat_of_unitLie C hZ σ
  have b := star_trace_mat_of_unitLie C hZ' σ
  have e1 := congrArg star e0
  rw [star_add, star_mul', a, b, star_zero, Complex.star_def, Complex.conj_I] at e1
  have hy : trace (mat Z' σ) = 0 := by
    have : (2 * I) * trace (mat Z' σ) = 0 := by linear_combination e0 + e1
    rcases mul_eq_zero.1 this with h2 | h2
    · exfalso; simp at h2
    · exact h2
  refine ⟨?_, hy⟩
  rw [hy, mul_zero, add_zero] at e0
  exact e0

theorem trLin_toLieC_of_trace {D : D7} {S T : HSp D} (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas)
    (hB : C.IsB B) (m : D.what₂.Tau → ℤ) (W : Frame C.X.Ψ T.rank) (hW : ∀ σ, trace (mat W σ) = 0) :
    trLin T m (toLieC C R B W) = 0 := by
  change ∑ ρ, (m ρ : ℂ) * trace ((toLieC C R B W) ρ).1 = 0
  refine Finset.sum_eq_zero fun ρ _ => ?_
  change (m ρ : ℂ) * trace ((GlobalTheory.HolRead.AdExt.toLie R B (fun ρ => C.m.e ρ) (conjL W)) ρ).1 = 0
  rw [GlobalTheory.HolRead.AdExt.toLie_val, mat_conjL]
  have hN : trace ((mat W (C.m.e ρ)).map (starRingEnd ℂ)) = 0 := by
    have : trace ((mat W (C.m.e ρ)).map (starRingEnd ℂ)) = starRingEnd ℂ (trace (mat W (C.m.e ρ))) := by
      simp [Matrix.trace, map_sum]
    rw [this, hW, map_zero]
  set N := (mat W (C.m.e ρ)).map (starRingEnd ℂ)
  have hM : trace (B ρ * N * (B ρ)⁻¹) = 0 := by
    rw [trace_mul_cycle, nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.one_mul, hN]
  have hC : trace (conjAt T ρ (B ρ * N * (B ρ)⁻¹)) = 0 := by
    unfold conjAt
    rw [trace_neg, trace_mul_cycle, mul_nonsing_inv _ (R.1 ρ).2, Matrix.one_mul, trace_conjTranspose, hM, star_zero,
      neg_zero]
  rw [trace_smul, trace_add, hM, hC]
  simp

theorem trLin_toLieC_unitFr : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (m : D.what₂.Tau → ℤ) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  intro D S T C R B hB m ρ c d hcd Z Z' hZ hZ' h
  rw [trLin_toLieC_of_trace C R B hB m Z (fun σ => (trace_mat_eq_zero_of_add_I C ρ c d hcd hZ hZ' h σ).1),
    trLin_toLieC_of_trace C R B hB m Z' (fun σ => (trace_mat_eq_zero_of_add_I C ρ c d hcd hZ hZ' h σ).2), mul_zero, add_zero]

end GlobalTheory.AdSpan.ConjHol
