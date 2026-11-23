import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SizesProof

theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < Formalism.MainNotions.S.vand x :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb => sub_pos.2 (h (Finset.mem_filter.1 hb).2)

theorem sizes_of_hyp : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b →
    HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 hb h
  obtain ⟨⟨-, -, hmf, hfk, -, -, -, -, -, -, -, hg1, hg1', hg2, hg2', -, -, -, hv, -, -, hgap, hT, hCl, hCl0⟩, -, -⟩ := h
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb1 : 1 < large₂.sc.b := lt_trans (by simpa using Real.exp_lt_exp.2 (zero_lt_one (α := ℝ))) hbe
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (1 : ℝ) ≤ D.R.k * large₂.sc.b := by nlinarith
  have h8 : (1 : ℝ) ≤ (D.R.k * large₂.sc.b) ^ 8 := one_le_pow₀ hkb
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 1 ≤ gg D := by unfold gg; nlinarith
  have hu : ∀ w τ, StrictAnti (uS D w τ) := fun w τ => by
    have hk0 : D.R.k = (D.R.k - 1) + 1 := by have := D.R.m_add_three_le_k; omega
    have key : ∀ (i : ℕ) (hi : i + 1 < D.R.k), uS D w τ ⟨i + 1, hi⟩ < uS D w τ ⟨i, by omega⟩ := fun i hi => by
      have a := (D.hcW w τ).u_gt_v ⟨i, by omega⟩
      have b := (D.hcW w τ).v_gt_u ⟨i, by omega⟩
      unfold uS; exact_mod_cast b.trans a
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih => exact (key c hc).trans (ih (by omega) hc')
  refine ⟨hL, Real.log_exp _, hbe, hm, hr, D.what₂.card_Tau, hCl, hmf.trans hfk, hv, hrd, rfl, hrd ▸ hb, hgg, ?_, ?_, ?_,
    fun w => (hT w).2, fun w τ => ⟨vand_pos (hu w τ), ?_⟩, ?_⟩
  · rw [two_mul, Real.rpow_add (by linarith)]
    exact mul_le_mul hg1' hg2' (by linarith) (by linarith)
  · have : large₂.sc.b ^ (8 : ℝ) ≤ large₂.sc.b ^ Cg := by
      refine le_trans ?_ (hg1.trans hg1')
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) (by nlinarith) 8
    exact (Real.rpow_le_rpow_left_iff hb1).1 this
  · refine le_trans ?_ (hg1.trans hg1')
    exact le_trans (by nlinarith) (le_self_pow₀ hkb (by norm_num))
  · have h1 : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    have h2 : 0 < D.host.rdE := by linarith
    have h3 : 0 < gg D := by linarith
    have h4 : 0 < VV D τ := mul_pos (D.dsig_pos τ) (Finset.prod_pos fun i _ => by positivity)
    have h5 := vand_pos (hu w τ)
    unfold Tcrit; positivity
  · intro τ
    have hp : 0 ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 := by positivity
    have key : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1),
        Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := fun i hi => by
      have := hgap τ ⟨i, by omega⟩ (by simpa [hr] using hi)
      have h0 : (0 : ℝ) ≤ D.R.r * (D.R.m : ℝ) ^ 10 := by positivity
      exact lt_of_le_of_lt (le_add_of_nonneg_right h0) this
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih =>
      have := key c hc
      have := ih (by omega) hc'
      linarith

end GlobalTheory.Amp.SizesProof
