import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.ElevenLe

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LoopBCovN

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def eN (D : D7) : ℝ := (D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) / 2

def CovNFormula : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), 0 < θ →
    LoopTerm.covN (Y := Y) C u = (θ * (2 * D.host.v) ^ eN D) ^ Fintype.card D.what₂.Tau

theorem rdE_ge_one (D : D7) : 1 ≤ 2 * D.host.v := by
  unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
    have h0 : NumberField.discr D.host.E ≠ 0 := NumberField.discr_ne_zero D.host.E
    have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h0
    exact_mod_cast h1
  have h2 : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ^ (1 / (Module.finrank ℚ D.host.E : ℝ)) :=
    Real.one_le_rpow hd (by positivity)
  linarith

theorem covWinN_of (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} (C : Choice X 1) (large₂ : SizeData₂ D) {C1 : ℝ}
    (hC1 : 0 ≤ C1) (hup : eN D * Real.log (2 * D.host.v) ≤ C1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b)
    (u u' : D.what₂.Word) : LoopTerm.CovWinN (Y := Y) C large₂ C1 u u' := by
  have hbpos : 0 < large₂.sc.b := by
    unfold Scale.b
    exact Real.exp_pos _
  have hv := rdE_ge_one D
  have hv0 : 0 < 2 * D.host.v := by linarith
  have heN : 0 ≤ eN D := by
    unfold eN
    positivity
  have hy1 : 1 ≤ (2 * D.host.v) ^ eN D := Real.one_le_rpow hv heN
  have hlog0 : 0 ≤ eN D * Real.log (2 * D.host.v) := mul_nonneg heN (Real.log_nonneg hv)
  have hyexp : (2 * D.host.v) ^ eN D = Real.exp (Real.log (2 * D.host.v) * eN D) :=
    Real.rpow_def_of_pos hv0 _
  have hcov : ∀ w, LoopTerm.covN (Y := Y) C w = ((2 * D.host.v) ^ eN D) ^ Fintype.card D.what₂.Tau := by
    intro w
    rw [hF D X Y 1 C w one_pos, one_mul]
  have hx : (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u') ^ (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) = 1 ∨
      (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u') ^ (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) =
        (2 * D.host.v) ^ eN D := by
    rw [hcov u, hcov u', ← pow_add, ← two_mul]
    rcases Nat.eq_zero_or_pos (Fintype.card D.what₂.Tau) with h0 | hpos
    · left
      simp [h0]
    · right
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      have hN : (0 : ℝ) < Fintype.card D.what₂.Tau := by exact_mod_cast hpos
      have h2 : ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ) * (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) = 1 := by
        push_cast
        field_simp
      rw [h2, Real.rpow_one]
  have hxb : ∀ z : ℝ, (z = 1 ∨ z = (2 * D.host.v) ^ eN D) → 1 ≤ z ∧ z ≤ (2 * D.host.v) ^ eN D := by
    rintro z (rfl | rfl) <;> exact ⟨by linarith, by linarith⟩
  obtain ⟨hx1, hx2⟩ := hxb _ hx
  have hup' : Real.log (2 * D.host.v) * eN D ≤ Real.log large₂.sc.b * (C1 * (D.R.m : ℝ) ^ 2) := by linarith
  unfold LoopTerm.CovWinN normWin
  refine ⟨le_trans ?_ hx1, le_trans hx2 ?_⟩
  · rw [Real.rpow_def_of_pos hbpos]
    have hneg : Real.log large₂.sc.b * -(C1 * (D.R.m : ℝ) ^ 2) ≤ 0 := by nlinarith
    exact Real.exp_le_one_iff.mpr hneg
  · rw [hyexp, Real.rpow_def_of_pos hbpos]
    exact Real.exp_le_exp.mpr hup'

theorem log_rd_le {D : D7} (large₂ : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt large₂) :
    Real.log (2 * D.host.v) ≤ Real.log large₂.sc.b / 72 := by
  obtain ⟨-, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have h2v : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  rw [h2v]
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have ht : (1 : ℝ) ≤ D.R.t := hT.1
  have hqd : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    have h1 : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hcond : D.host.rdE ≤ Formalism.MainNotions.szCond large₂ := by
    unfold Formalism.MainNotions.szCond
    calc D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) := hr2
      _ ≤ (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := by gcongr
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
        have h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
        nlinarith
  have hc1 : (1 : ℝ) ≤ Formalism.MainNotions.szCond large₂ := le_trans hr1 hcond
  have hb0 : 0 < large₂.sc.b := lt_of_lt_of_le (by norm_num) (Formalism.MainNotions.S.two_le_scb large₂)
  have h36 : Formalism.MainNotions.szCond large₂ ^ 36 ≤ Real.sqrt large₂.sc.b := by
    have : Formalism.MainNotions.szCond large₂ ^ 36 ≤ Formalism.MainNotions.szCond large₂ ^ 36 * (D.R.t : ℝ) ^ 150 := by
      have : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht
      nlinarith [pow_pos (lt_of_lt_of_le one_pos hc1) 36]
    exact this.trans hC
  have hl := Real.log_le_log (pow_pos (lt_of_lt_of_le one_pos hc1) 36) h36
  rw [Real.log_pow, Real.log_sqrt hb0.le] at hl
  have hl2 := Real.log_le_log (lt_of_lt_of_le one_pos hr1) hcond
  push_cast at hl
  linarith

theorem eN_le (D : D7) : eN D ≤ (D.R.m : ℝ) ^ 2 / 2 := by
  unfold eN
  have h : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) / 2 := by
    have : 2 * D.R.rS ≤ D.R.m := by unfold Formalism.BasicNotions.Ranks.rS; omega
    have : (2 * D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast this
    linarith
  have h0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  nlinarith

theorem covWinN_sizes (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} (C : Choice X 1) (large₂ : SizeData₂ D)
    (hS : Formalism.MainNotions.SizesAt large₂) {C1 : ℝ} (hC1 : 1 / 144 ≤ C1) (u u' : D.what₂.Word) :
    LoopTerm.CovWinN (Y := Y) C large₂ C1 u u' := by
  have hv := rdE_ge_one D
  have hl0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg hv
  have hl := log_rd_le large₂ hS
  have he := eN_le D
  have hb : 0 ≤ Real.log large₂.sc.b := by linarith
  have hm : 0 ≤ (D.R.m : ℝ) ^ 2 := by positivity
  refine covWinN_of hF C large₂ (by linarith) ?_ u u'
  calc eN D * Real.log (2 * D.host.v) ≤ ((D.R.m : ℝ) ^ 2 / 2) * (Real.log large₂.sc.b / 72) :=
        mul_le_mul he hl hl0 (by positivity)
    _ = 1 / 144 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by ring
    _ ≤ C1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by
        apply mul_le_mul_of_nonneg_right _ hb
        exact mul_le_mul_of_nonneg_right hC1 hm

theorem covN_pos (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} {θ : ℝ} (hθ : 0 < θ) (C : Choice X θ)
    (u u' : D.what₂.Word) : 0 < LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' := by
  rw [hF D X Y θ C u hθ, hF D X Y θ C u' hθ]
  have h1 := rdE_ge_one D
  have h2 : 0 < θ * (2 * D.host.v) ^ eN D := mul_pos hθ (Real.rpow_pos_of_pos (by linarith) _)
  exact mul_pos (pow_pos h2 _) (pow_pos h2 _)

end Formalism.L2.SG.Pf.LoopBCovN
