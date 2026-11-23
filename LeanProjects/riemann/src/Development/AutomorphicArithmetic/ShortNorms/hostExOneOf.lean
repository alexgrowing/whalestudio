import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AutomorphicArithmetic.CharacterBoxes.Imports
import Development.AutomorphicArithmetic.CharacterBoxes.PairHyp
import Development.AutomorphicArithmetic.MeanSquareBounds.pairEx
import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi
import Development.AutomorphicArithmetic.CoprimeRanks.FieldAny

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.HC GlobalTheory.EX UpperTheory.Top HostParam.Seam

theorem UpperTheory.T3.hostExOneOf :
    (∀ eps C0 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C0 → ∃ CT2 C8 c6 Cb x0 : ℝ, C0 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧
      ∀ (s : Scale) (R : Ranks) (H0 : HostAx R.toFrame) (M : ℕ) (Y : ℝ), s.eps = eps → x0 ≤ s.x → RankVal s R →
        s.J ≤ C0 → (R.o : ℝ) ≤ C0 → (H0.QS : ℝ) ≤ C0 * R.n → 0 < M → (M : ℝ) ≤ C0 → H0.QS ∣ Nat.lcm (2 ^ (R.e + 2)) M →
        PairWin s Y → PairGood M eps Y s.x H0.q H0.d → FieldRows H0.toHostRaw ⌊Y ^ (eps / 5)⌋₊ → admitted R H0 →
        ∃ (H : Host R) (q0 : ℕ), H.toHostAx = H0 ∧ H.CT2 = CT2 ∧ HostGood s C8 4 c6 Cb H q0 ∧
          R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps))) → GlobalTheory.EX.HostEx := by
  intro h
  refine ⟨2, by norm_num, fun eps h0 h1 => ?_⟩
  obtain ⟨CT2, C8, c6, Cb, x0, hC, hc6, hCb, h⟩ := h eps 4 h0 h1 (by norm_num)
  obtain ⟨Y1, hY1⟩ := QH.pairEx 1 one_pos eps 1 h0 h1 le_rfl
  obtain ⟨x1, hx1⟩ := admissibleClassesTwistedChar eps h0 h1
  obtain ⟨x2, hx2⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by positivity : 0 < eps / 5)).eventually_ge_atTop 8)
  refine ⟨CT2, C8, 4, c6, Cb, max (max x0 Y1) (max (max x1 x2) 4), by linarith, by norm_num, hc6, hCb,
    Scales.univ 2 1 le_rfl, fun s hs hx hS => ?_⟩
  have hJ : s.J = 1 := Scales.mem_univ.1 hS
  simp only [max_le_iff] at hx
  obtain ⟨⟨a0, aY⟩, ⟨a1, a2⟩, a4⟩ := hx
  obtain ⟨q, d, hP⟩ := hY1 s.x aY
  rw [Real.rpow_one] at hP
  obtain ⟨hyp, hsp, -⟩ := pairHyp eps s.x q d hP.pair
  have hz := hx2 s.x a2
  have hcard : Nat.card (⊥ : Subgroup (DirichletCharacter ℂ 1)) = 1 := Subgroup.card_bot
  have hW : s.x ≤ s.x ^ (2 + 8 * s.eps) := by
    have := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (show (1 : ℝ) ≤ 2 + 8 * s.eps by linarith [s.eps_pos])
    rwa [Real.rpow_one] at this
  obtain ⟨e, he2, w1, w2⟩ := (anyFrame_window (⊥ : Subgroup (DirichletCharacter ℂ 1))).2.2 2 (s.x ^ (2 + 8 * s.eps))
    (by rw [hcard]; push_cast; linarith)
  have he : 4 * 1 ≤ 2 ^ e := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos he2)
  have hq3 : q ≠ 3 := by
    rintro rfl
    have b1 := hP.pair.q_lo.trans_le (Real.log_le_self (Nat.cast_nonneg _))
    push_cast at b1
    linarith
  obtain ⟨φ, H0, f1, f2, f3, f4, f5, f6, f7, f8, -⟩ :=
    exists_fieldRows_any_ord (⊥ : Subgroup (DirichletCharacter ℂ 1)) (e := e) (b := ⌊s.x ^ (eps / 5)⌋₊) hyp hq3
      hP.coprime he (by rw [hcard, one_pow]; exact Nat.one_le_two_pow) (Nat.le_floor (by push_cast; linarith))
      fun p hp hp2 hpb => hsp p hp hp2 ((Nat.le_floor_iff (by linarith)).1 hpb)
  rw [← f1] at w1 w2
  obtain ⟨R, rfl, hR, hA⟩ := hx1 s φ H0 hs a1 w1 w2
  subst f2 f3 f4
  obtain ⟨H, q0, -, g2, g3, -⟩ := h s R H0 1 s.x hs a0 hR (by rw [hJ]; norm_num)
    (by have : R.o = 1 := f5.trans hcard
        rw [this]; norm_num)
    (by exact_mod_cast f8) one_pos (by norm_num) f7
    ⟨by rw [hJ, div_one, Real.rpow_one], le_rfl⟩ hP f6 hA
  exact ⟨R, H, q0, hR, g2, g3, trivial⟩
