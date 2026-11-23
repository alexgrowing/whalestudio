import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTParNums
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem
import Formalism.PeriodIntegrals.IsLowUnitH

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

def CapFromHC : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (u : Fin k → ℝ) (π : Formalism.FourierDecayAlt.Q.Mx k r → (Wp →L[ℂ] Wp)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π → ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z) →
    PI.UpqRep.IsHCTypeW k r z u π →
    Formalism.FourierDecayAlt.Q.CapParam k r z π (fun i => if h : i - 1 < k then u ⟨i - 1, h⟩ else 0)

section Block

variable {k r : ℕ}

theorem mvs {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : (M *ᵥ Pi.single j (1 : ℂ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem blockW_fix (h : Matrix (Fin k) (Fin k) ℂ) (j : Fin (2 * r + k + 1)) (hj : ¬ (r ≤ j.val ∧ j.val < r + k)) :
    Formalism.MainNotions.S.blockW k r h *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j := by
  funext i
  unfold Formalism.QuantumDeterminants.bvec
  rw [mvs]
  unfold Formalism.MainNotions.S.blockW
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · rw [dif_pos hi, dif_neg hj, Pi.single_apply, if_neg]
    intro e; rw [e] at hi; exact hj hi
  · rw [dif_neg hi, Pi.single_apply]

theorem blockW_UH (h : Matrix (Fin k) (Fin k) ℂ) (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  show (Formalism.MainNotions.S.blockW k r h)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.QuantumDeterminants.Hpk k r
  have hs : hᴴ * h = 1 := Matrix.mem_unitaryGroup_iff'.mp hh
  have e1 : (Formalism.MainNotions.S.blockW k r h)ᴴ = Formalism.MainNotions.S.blockW k r hᴴ := PI.HwUniqW.blockW_conjTranspose h
  have e2 : Formalism.QuantumDeterminants.Hpk k r * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r h * Formalism.QuantumDeterminants.Hpk k r :=
    PI.HwUniqW.Hpk_blockW_comm h
  have e3 : Formalism.MainNotions.S.blockW k r hᴴ * Formalism.MainNotions.S.blockW k r h = Formalism.MainNotions.S.blockW k r (hᴴ * h) :=
    PI.HwUniqW.blockW_mul hᴴ h
  have e4 : Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := PI.HwUniqW.blockW_one
  rw [e1, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, e3, hs, e4, Matrix.one_mul]

theorem conj_blockW_mem {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : Formalism.MainNotions.S.IsFrameW k r z g) (h : Matrix (Fin k) (Fin k) ℂ) (hh : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g * Formalism.MainNotions.S.blockW k r h * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := by
  obtain ⟨hgU, hge, hgz⟩ := hg
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hgU
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hgU
  have hinv : ∀ x, g *ᵥ x = x → g⁻¹ *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  have hfix : ∀ x, g *ᵥ x = x → Formalism.MainNotions.S.blockW k r h *ᵥ x = x → (g * Formalism.MainNotions.S.blockW k r h * g⁻¹) *ᵥ x = x :=
    fun x h1 h2 => by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv x h1, h2, h1]
  refine ⟨PI.HwUniqW.mul_mem_UH (PI.HwUniqW.mul_mem_UH hgU (blockW_UH h hh)) (PI.HwUniqW.inv_mem_UH hgU),
    fun a => ⟨hfix _ (hge a).1 (blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.eI]; omega)),
      hfix _ (hge a).2 (blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.esI]; omega))⟩, ?_⟩
  have hx : ∀ x, g⁻¹ *ᵥ (g *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
  rw [← hgz, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul,
    blockW_fix h _ (by simp only [Formalism.QuantumDeterminants.wI, Fin.val_last]; omega)]

end Block

theorem isType_of_hc (hcap : CapFromHC) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.Q.Mx k r → (Wp →L[ℂ] Wp)}
    (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hHC : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UWset k r z) π ∧
      (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ x, ‖π h x‖ = ‖x‖) ∧ ContinuousOn π (Formalism.QuantumDeterminants.UWset k r z))
    (w : ℕ → ℝ) (hw : ∀ i ∈ Finset.Icc 1 k, w i = if h : i - 1 < k then u ⟨i - 1, h⟩ else 0) :
    Formalism.FourierDecayAlt.Q.IsType k r z π w := by
  obtain ⟨g, hg, hU⟩ := hHC
  refine ⟨hU.1, hrep.1, hrep.2.2, hrep.2.1, fun S hS => ?_, ?_⟩
  · have hK := hU.2.2.2.2.2.1 S le_top (fun h hh v hv => hS _ (conj_blockW_mem hg h hh.1) v hv)
    exact hK
  · intro Bs hBs x v
    rw [hcap Wp k r z u π hz hT hrep.1 hrep.2.2 ⟨g, hg, hU⟩ Bs hBs x v]
    congr 1
    exact Finset.prod_congr rfl fun i hi => by rw [hw i hi]

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
