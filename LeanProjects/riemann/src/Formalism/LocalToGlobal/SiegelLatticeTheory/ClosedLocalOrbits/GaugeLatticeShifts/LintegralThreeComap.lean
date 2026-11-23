import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MemOmLoc

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.L2.SG.RealObj.EnergyIntOm Formalism.L2.SG.Pf.WuBL
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem sigC_Tm (C : Choice X θ) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    sigB X (Qcs C τ) (Qics C τ) τ (Matrix.of (Tm C τ y)) = X.B.σ (vOf X τ) (uMat y) := by
  have h2 := (transpC' C τ).2.1
  show X.B.σ (vOf X τ) (Qcs C τ * (Qics C τ * uMat y * Qcs C τ) * Qics C τ) = _
  rw [show Qcs C τ * (Qics C τ * uMat y * Qcs C τ) * Qics C τ = (Qcs C τ * Qics C τ) * uMat y * (Qcs C τ * Qics C τ) by
    simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]

theorem lintegral_four_comap (C : Choice X θ) (τ : D.what₂.Tau) {ν0 ν0' μ1 μ1' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (h0 : ν0 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h0' : ν0' {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1 : μ1 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1' : μ1' {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (G : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS →
      Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ x', ∫⁻ s, ∫⁻ s', G (Tm C τ x) (Tm C τ x') (Tm C τ s) (Tm C τ s')
      ∂(μ1'.comap (Tm C τ)) ∂(μ1.comap (Tm C τ)) ∂(ν0'.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) =
    ∫⁻ m, ∫⁻ m', ∫⁻ p, ∫⁻ p', G m m' p p' ∂μ1' ∂μ1 ∂ν0' ∂ν0 := by
  rw [← comap_lint C τ h0 (fun m => ∫⁻ m', ∫⁻ p, ∫⁻ p', G m m' p p' ∂μ1' ∂μ1 ∂ν0')]
  refine lintegral_congr fun x => ?_
  rw [← comap_lint C τ h0' (fun m' => ∫⁻ p, ∫⁻ p', G (Tm C τ x) m' p p' ∂μ1' ∂μ1)]
  refine lintegral_congr fun x' => ?_
  rw [← comap_lint C τ h1 (fun p => ∫⁻ p', G (Tm C τ x) (Tm C τ x') p p' ∂μ1')]
  refine lintegral_congr fun s => ?_
  rw [← comap_lint C τ h1' (fun p' => G (Tm C τ x) (Tm C τ x') (Tm C τ s) p')]

theorem lintegral_three_comap (C : Choice X θ) (τ : D.what₂.Tau) {ν0 μ1 : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)}
    (h0 : ν0 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (h1 : μ1 {m | Matrix.of m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0)
    (G : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ x', ∫⁻ s, G (Tm C τ x) (Tm C τ x') (Tm C τ s)
      ∂(μ1.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) ∂(ν0.comap (Tm C τ)) =
    ∫⁻ m, ∫⁻ m', ∫⁻ p, G m m' p ∂μ1 ∂ν0 ∂ν0 := by
  rw [← comap_lint C τ h0 (fun m => ∫⁻ m', ∫⁻ p, G m m' p ∂μ1 ∂ν0)]
  refine lintegral_congr fun x => ?_
  rw [← comap_lint C τ h0 (fun m' => ∫⁻ p, G (Tm C τ x) m' p ∂μ1)]
  refine lintegral_congr fun x' => ?_
  rw [← comap_lint C τ h1 (fun p => G (Tm C τ x) (Tm C τ x') p)]

end Formalism.L2.SG.RealObj.EnergyConvJ
