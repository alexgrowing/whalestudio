import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SumSize.TopInt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def primeUnder (w : PlL D) : ℕ := ringChar (𝓞 D.what₂.LL ⧸ w.asIdeal)

theorem primeUnder_mem (w : PlL D) : ((primeUnder w : ℕ) : 𝓞 D.what₂.LL) ∈ w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem primeUnder_prime (w : PlL D) : (primeUnder w).Prime := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (𝓞 D.what₂.LL ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  exact CharP.char_is_prime (𝓞 D.what₂.LL ⧸ w.asIdeal) (ringChar (𝓞 D.what₂.LL ⧸ w.asIdeal))

def kerLoss (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (X Y : Node) (l n : ℕ) : ℝ :=
  (((∑ τ, ∑ a, (wt G Y τ).natW a : ℕ) : ℝ) + (D.R.f : ℝ) * (G.V X).rank * (G.V Y).rank) *
      (δ l + (if l = D.host.d then 1 else 0) + n) +
    (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (if (l : ℝ) ≤ C1 * b then Real.logb l (C1 * b) else 0)

def topDl (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (w : PlL D) : ℝ :=
  (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 *
    ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) (depL G (primeUnder w))

theorem vw_natCast_nonneg (w : PlL D) (n : ℕ) : 0 ≤ vw w ((n : ℕ) : D.what₂.LL) := by
  have e : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) ((n : ℕ) : D.what₂.LL) =
      ((Ideal.span {((n : ℕ) : 𝓞 D.what₂.LL)} : Ideal (𝓞 D.what₂.LL)) : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, map_natCast]
  unfold vw
  rw [e]
  exact FractionalIdeal.count_coe_nonneg _ _ _

theorem kerLoss_nonneg (G : GridData L sc) {δ : ℕ → ℝ} (hδ : ∀ l, 0 ≤ δ l) (C1 b : ℝ) (X Y : Node) {l : ℕ} (hl : l.Prime)
    (n : ℕ) : 0 ≤ kerLoss G δ C1 b X Y l n := by
  unfold kerLoss
  have h1 : 0 ≤ (if l = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have h2 : 0 ≤ (if (l : ℝ) ≤ C1 * b then Real.logb l (C1 * b) else 0) := by
    split_ifs with h
    · exact Real.logb_nonneg (by exact_mod_cast hl.one_lt) (le_trans (by exact_mod_cast hl.one_lt.le) h)
    · exact le_rfl
  have := hδ l
  positivity

theorem kerLoss_mono (G : GridData L sc) (δ : ℕ → ℝ) (C1 b : ℝ) (X Y : Node) (l : ℕ) {n n' : ℕ} (h : n ≤ n') :
    kerLoss G δ C1 b X Y l n ≤ kerLoss G δ C1 b X Y l n' := by
  unfold kerLoss
  have : (n : ℝ) ≤ n' := by exact_mod_cast h
  gcongr

theorem le_topDl (G : GridData L sc) {δ : ℕ → ℝ} (hδ : ∀ l, 0 ≤ δ l) {C1 : ℝ} (hC1 : 0 ≤ C1) (b : ℝ) (w : PlL D) {j : ℕ}
    (hj : j < D.R.m) {n : ℕ} (hn : n ≤ depL G (primeUnder w)) :
    (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 * kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) n ≤
      topDl G δ C1 b w := by
  unfold topDl
  have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * C1 :=
    mul_nonneg (by exact_mod_cast vw_natCast_nonneg w _) hC1
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine le_trans (kerLoss_mono G δ C1 b _ _ _ hn) ?_
  exact Finset.single_le_sum (f := fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) (primeUnder w) (depL G (primeUnder w)))
    (fun j _ => kerLoss_nonneg G hδ C1 b _ _ (primeUnder_prime w) _) (Finset.mem_range.2 hj)

theorem inLat_mono {n : ℕ} {lam : D.what₂.Tau → DomWeight n} {w : PlL D} {a a' : ℝ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {v : VV ℂ lam} (h : InLat lam w a Λ v) (ha : a ≤ a') : InLat lam w a' Λ v := by
  obtain ⟨u, s, h1, h2, h3, h4⟩ := h
  exact ⟨u, s, h1, h2, h3.trans ha, h4⟩

end GlobalTheory.SumSize.TopInt

end
