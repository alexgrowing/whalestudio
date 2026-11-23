import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGConstSmul
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2RightTranslationThm

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf.GoodS

theorem nu_conc {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hS : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS) (hq : Formalism.MainNotions.S.IsQuotMeas μG μS ν) :
    ν {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} = 0 := by
  classical
  have hUH : ∀ a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro a b ha hb
    have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
    have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
    show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']
  have hSG : ∀ M, M ∈ Formalism.QuantumDeterminants.Sset k r z → M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    rintro M ⟨g, hg, m, hm, rfl⟩
    exact hUH g m hg.1 hm.1
  have hc : Continuous fun x : Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x := by
    have h0 : Continuous fun x : Formalism.QuantumDeterminants.Mt k r => Matrix.of x := continuous_id
    exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
  have hBm : MeasurableSet
      {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
    have hcl : IsClosed {x : Formalism.QuantumDeterminants.Mt k r |
        (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r} :=
      isClosed_eq hc continuous_const
    exact hcl.measurableSet.compl
  have hq1 := hq
    ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
      fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hBm)
  rw [lintegral_indicator_const hBm, hG.2.2.1, mul_zero] at hq1
  have hpt : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
        fun _ => μS Set.univ) x ≤
      ∫⁻ s, ({x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}.indicator
        fun _ => (1 : ℝ≥0∞)) (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
    · have hnm : x ∉ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} :=
        fun h => h hx
      rw [Set.indicator_apply, if_neg hnm]
      exact bot_le
    · have hxm : x ∈ {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := hx
      rw [Set.indicator_apply, if_pos hxm]
      calc μS Set.univ = ∫⁻ _, (1 : ℝ≥0∞) ∂μS := lintegral_one.symm
        _ ≤ _ := by
          apply lintegral_mono_ae
          have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Formalism.QuantumDeterminants.Sset k r z := ae_iff.mpr hS.2.2.1
          filter_upwards [hae] with s hs
          have hsG : (Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of s = Formalism.QuantumDeterminants.Hpk k r :=
            hSG _ hs
          have hmem : (fun i j => (Matrix.of s * Matrix.of x) i j) ∈
              {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} := by
            show ¬ (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j) ∈
              Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
            intro hG'
            have e : (Matrix.of s * Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r *
                (Matrix.of s * Matrix.of x) = Formalism.QuantumDeterminants.Hpk k r := hG'
            apply hx
            show (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x = Formalism.QuantumDeterminants.Hpk k r
            rw [Matrix.conjTranspose_mul] at e
            calc (Matrix.of x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of x
                = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Formalism.QuantumDeterminants.Hpk k r * Matrix.of s) *
                    Matrix.of x := by rw [hsG]
              _ = Formalism.QuantumDeterminants.Hpk k r := by simpa only [Matrix.mul_assoc] using e
          simp only [Set.indicator_of_mem hmem, le_refl]
  have hle := lintegral_mono (μ := ν) hpt
  rw [lintegral_indicator_const hBm, ← hq1] at hle
  have hpos : μS Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr hS.2.1).ne'
  rcases mul_eq_zero.mp (nonpos_iff_eq_zero.mp hle) with h | h
  · exact absurd h hpos
  · exact h

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (m : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    phiOf hB u τ m = wT C u τ (m * C.y τ) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy := C.y_mem τ
  obtain ⟨hrep, -⟩ := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models _ _ hm hy
  have hJ : (C.Q τ * (m * C.y τ) * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * (m * C.y τ) * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    have hmy' : (m * C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (m * C.y τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hmy
    calc (C.Q τ * (m * C.y τ) * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * (m * C.y τ) * C.Qi τ)
        = (C.Qi τ)ᴴ * ((m * C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * (m * C.y τ)) *
            C.Qi τ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hmy', qiHqi _ h2 hg]
  set γ := toUJn (C.Q τ * (m * C.y τ) * C.Qi τ) hJ
  have hγ : uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ := rfl
  have hW := (hB u τ).choose_spec.2 γ
  have e1 : sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ) = X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ)) := by
    unfold v0Of
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hm _ hy, hγ]
    rfl
  unfold phiOf bOf
  rw [e1, ← hW, ← Formalism.L2.SG.Pf.WuBL.wT_at C u τ γ, hγ]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem l2SG_phiOf_ne_zero_and_lt_infty (C : Choice X θ) (hLF : LocFactor C) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 ∧ l2SG (C.nuS u τ) (phiOf hB u τ) < ⊤ := by
  obtain ⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩ := hLF u τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  have hHG := Formalism.L2.SG.Pf.haarTr C τ
  have hq := C.nuS_q u τ
  have hy := C.y_mem τ
  have hconc := nu_conc hz hT hHG hSH hq
  have hπ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT (Formalism.L2.SG.Pf.colsTypeTr C u τ)
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
    rintro _ ⟨h0, hh0, n0, hn0, rfl⟩ x hx
    rw [hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, Formalism.L2.SG.Pf.WuBL.norm_psi, one_mul, hπ.2.1 h0 hh0]
  have heq := Formalism.L2.SG.Pf.WuBL.l2RightTranslation_thm D.R.k D.R.rS _ hz hT _ _ _ hHG hSH hq _ (wT C u τ) hWc
    (Formalism.L2.SG.Pf.WuBL.wT_off C u τ) hinv (C.y τ) hy
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  have hphi : l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) := by
    unfold l2SG
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [phi_eq C hB u τ _ hx]
  rw [hphi, heq]
  exact ⟨hne, hfin⟩

end Formalism.L2.SG.Pf.GoodS
