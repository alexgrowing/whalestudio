import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.LeadMinorEZhatOMNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBoundTwo
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem rdE_pos' : 0 < D.host.rdE := lt_of_lt_of_le zero_lt_one (one_le_rdE D)

theorem one_le_prod_norm (x : D.host.E) (hx : x ∈ intS D) (h0 : x ≠ 0) : 1 ≤ ∏ τ, ‖embS D τ x‖ :=
  Formalism.MainNotions.BesselShellMomentBounds.prod_absV_ge_one D x hx h0

theorem norm_embS_pos {x : D.host.E} (h0 : x ≠ 0) (τ : D.what₂.Tau) : 0 < ‖embS D τ x‖ :=
  norm_pos_iff.mpr ((map_ne_zero _).mpr h0)

def qS : ℝ := D.host.rdE ^ (-(D.R.rS : ℝ))

theorem qS_pos : 0 < qS D := Real.rpow_pos_of_pos (rdE_pos' D) _

theorem qS_le_one : qS D ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_rdE D) (by have : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _; linarith)

theorem rhoF_le_one (a : Fin (D.R.rS + 1)) : rhoF D a ≤ 1 := by
  unfold rhoF
  apply Real.rpow_le_one_of_one_le_of_nonpos (one_le_rdE D)
  have : ((a : ℕ) : ℝ) ≤ D.R.rS := by exact_mod_cast Nat.lt_succ_iff.1 a.2
  linarith

theorem qS_le_rhoF (a : Fin (D.R.rS + 1)) : qS D ≤ rhoF D a := by
  unfold rhoF qS
  apply Real.rpow_le_rpow_of_exponent_le (one_le_rdE D)
  have : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

theorem rhoF_pos' (a : Fin (D.R.rS + 1)) : 0 < rhoF D a :=
  lt_of_lt_of_le (qS_pos D) (qS_le_rhoF D a)

def R0 : ℝ := ((qS D)⁻¹) ^ (2 * (D.R.rS + 1))

theorem one_le_R0 : 1 ≤ R0 D :=
  one_le_pow₀ ((one_le_inv₀ (qS_pos D)).mpr (qS_le_one D))

def rhoIJ {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1)) : ℝ := ∏ a, (rhoF D (I a) * rhoF D (J a))

theorem rhoIJ_pos {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1)) : 0 < rhoIJ D I J :=
  Finset.prod_pos fun a _ => mul_pos (rhoF_pos' D _) (rhoF_pos' D _)

theorem rhoIJ_le_one {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1)) : rhoIJ D I J ≤ 1 :=
  Finset.prod_le_one (fun a _ => (mul_pos (rhoF_pos' D _) (rhoF_pos' D _)).le)
    (fun a _ => mul_le_one₀ (rhoF_le_one D _) (rhoF_pos' D _).le (rhoF_le_one D _))

theorem rhoIJ_inv_le {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1)) : (rhoIJ D I J)⁻¹ ≤ R0 D := by
  have hj : j ≤ D.R.rS + 1 := by
    simpa using Fintype.card_le_of_embedding I.toEmbedding
  have hq := qS_pos D
  have hq1 := qS_le_one D
  have h1 : (qS D * qS D) ^ j ≤ rhoIJ D I J := by
    unfold rhoIJ
    calc (qS D * qS D) ^ j = ∏ _a : Fin j, (qS D * qS D) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod (fun a _ => (mul_pos hq hq).le)
          (fun a _ => mul_le_mul (qS_le_rhoF D _) (qS_le_rhoF D _) hq.le (rhoF_pos' D _).le)
  have h2 : (qS D * qS D) ^ (D.R.rS + 1) ≤ (qS D * qS D) ^ j :=
    pow_le_pow_of_le_one (mul_pos hq hq).le (mul_le_one₀ hq1 hq.le hq1) hj
  have h3 : 0 < (qS D * qS D) ^ (D.R.rS + 1) := pow_pos (mul_pos hq hq) _
  calc (rhoIJ D I J)⁻¹ ≤ ((qS D * qS D) ^ (D.R.rS + 1))⁻¹ := inv_anti₀ h3 (h2.trans h1)
    _ = R0 D := by unfold R0; rw [inv_pow, ← sq, ← pow_mul]

theorem absMinor_eq {j : ℕ} (Z : GramM D) (I J : Fin j ↪o Fin (D.R.rS + 1)) (τ : D.what₂.Tau) :
    Formalism.MainNotions.S.UnitaryVolumeMass.absMinor D Z I J τ = ‖embS D τ (Z.submatrix I J).det‖ * rhoIJ D I J := rfl

theorem frameExp_le (l : ℕ) (hl : l ≤ D.R.rS + 1) : frameExp D.R.rS l ≤ (D.R.rS + 1) ^ 2 := by
  unfold frameExp
  calc ∑ a ∈ Finset.Icc 1 l, (D.R.rS + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 l, (D.R.rS + 1) :=
        Finset.sum_le_sum fun a _ => Nat.sub_le _ _
    _ = l * (D.R.rS + 1) := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]; congr 1
    _ ≤ (D.R.rS + 1) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hl

def R1 : ℝ := D.host.rdE ^ (2 * ((D.R.rS : ℝ) + 1) ^ 2)

theorem one_le_R1 : 1 ≤ R1 D := Real.one_le_rpow (one_le_rdE D) (by positivity)

theorem norm_le_absDl (Z : GramM D) (l : ℕ) (hl : l ≤ D.R.rS + 1) (τ : D.what₂.Tau) :
    ‖embS D τ (leadMinorE Z l)‖ ≤ absDl D Z l τ * R1 D := by
  unfold absDl absReal R1
  have hrd := rdE_pos' D
  have e : ‖embS D τ (leadMinorE Z l)‖ = ‖embS D τ (leadMinorE Z l)‖ *
      D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) * D.host.rdE ^ (2 * (frameExp D.R.rS l : ℝ)) := by
    rw [mul_assoc, ← Real.rpow_add hrd]; simp
  have hexp : D.host.rdE ^ (2 * (frameExp D.R.rS l : ℝ)) ≤ D.host.rdE ^ (2 * ((D.R.rS : ℝ) + 1) ^ 2) := by
    apply Real.rpow_le_rpow_of_exponent_le (one_le_rdE D)
    have := frameExp_le D l hl
    have h2 : (frameExp D.R.rS l : ℝ) ≤ ((D.R.rS : ℝ) + 1) ^ 2 := by exact_mod_cast this
    linarith
  calc ‖embS D τ (leadMinorE Z l)‖ = ‖embS D τ (leadMinorE Z l)‖ *
        D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) * D.host.rdE ^ (2 * (frameExp D.R.rS l : ℝ)) := e
    _ ≤ ‖embS D τ (leadMinorE Z l)‖ * D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) *
          D.host.rdE ^ (2 * ((D.R.rS : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hrd.le _))

theorem max_one_le_mul {H x : ℝ} (hH : 1 ≤ H) (hx : 0 ≤ x) : max 1 x ≤ H * max 1 (x / H) := by
  have hH0 : 0 < H := by linarith
  have e : H * max 1 (x / H) = max H x := by
    rw [mul_max_of_nonneg _ _ hH0.le, mul_one, mul_div_cancel₀ _ hH0.ne']
  rw [e]
  exact max_le_max hH le_rfl

theorem leading_minor_embedding_bound (Z : GramM D) (b C : ℝ) (hb : 1 ≤ b) (hC : 0 ≤ C) (τ : D.what₂.Tau) (l : ℕ)
    (hl : l ∈ Finset.Icc 1 (D.R.rS + 1)) : max 1 ‖embS D τ (leadMinorE Z l)‖ ≤
      (R1 D * b ^ (C * (D.R.m : ℝ) ^ 2)) * max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := by
  have hH : 1 ≤ b ^ (C * (D.R.m : ℝ) ^ 2) := Real.one_le_rpow hb (by positivity)
  have hR := one_le_R1 D
  have hl' : l ≤ D.R.rS + 1 := (Finset.mem_Icc.1 hl).2
  have h0 : 0 ≤ absDl D Z l τ := by
    unfold absDl absReal; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (rdE_pos' D).le _)
  calc max 1 ‖embS D τ (leadMinorE Z l)‖ ≤ max 1 (absDl D Z l τ * R1 D) := max_le_max le_rfl (norm_le_absDl D Z l hl' τ)
    _ ≤ R1 D * max 1 (absDl D Z l τ) := by
        rw [mul_comm]
        refine le_trans (max_mul_le (by linarith) h0) ?_
        rw [max_eq_right hR]
    _ ≤ R1 D * (b ^ (C * (D.R.m : ℝ) ^ 2) * max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left (max_one_le_mul hH h0) (by linarith)
    _ = _ := by ring

theorem prod_lead_le (Z : GramM D) (b C : ℝ) (hb : 1 ≤ b) (hC : 0 ≤ C) (τ : D.what₂.Tau) :
    ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 ‖embS D τ (leadMinorE Z l)‖ ≤
      (R1 D * b ^ (C * (D.R.m : ℝ) ^ 2)) ^ (D.R.rS + 1) * Formalism.MainNotions.GramProductBounds.Pt D b C Z τ := by
  have hH : 1 ≤ b ^ (C * (D.R.m : ℝ) ^ 2) := Real.one_le_rpow hb (by positivity)
  have hR := one_le_R1 D
  unfold Formalism.MainNotions.GramProductBounds.Pt
  have hc : (Finset.Icc 1 (D.R.rS + 1)).card = D.R.rS + 1 := by simp
  have step : ∀ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 ‖embS D τ (leadMinorE Z l)‖ ≤
      (R1 D * b ^ (C * (D.R.m : ℝ) ^ 2)) * max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := by
    intro l hl
    exact leading_minor_embedding_bound D Z b C hb hC τ l hl
  calc ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 ‖embS D τ (leadMinorE Z l)‖
      ≤ ∏ l ∈ Finset.Icc 1 (D.R.rS + 1),
          ((R1 D * b ^ (C * (D.R.m : ℝ) ^ 2)) * max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))) :=
        Finset.prod_le_prod (fun l _ => le_trans zero_le_one (le_max_left _ _)) step
    _ = (R1 D * b ^ (C * (D.R.m : ℝ) ^ 2)) ^ (Finset.Icc 1 (D.R.rS + 1)).card *
          ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = _ := by rw [hc]

end Formalism.MainNotions.S.Pv.HH

end
