import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

namespace FullerData

variable (D : FullerData II Ψ K ι Ω E Em)

def hodgeNormSq (z : (Σ k, ι k) → ℂ) (v : Fin D.N → Em) : ℝ :=
  ∑ τ, 2 * ‖D.herm.emb τ D.herm.ξ‖ *
    ∑ a, ‖((D.per z τ)⁻¹ *ᵥ fun b => D.herm.emb τ (v b)) a‖ ^ 2

def lam1 (z : (Σ k, ι k) → ℂ) : ℝ :=
  sInf {x : ℝ | ∃ v ∈ D.herm.L, v ≠ 0 ∧ x = Real.sqrt (D.hodgeNormSq z v)}

end FullerData

def rootDiscr (Em : Type) [Field Em] [NumberField Em] : ℝ :=
  |(discr Em : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ Em : ℝ))

def LamOneChart.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ a, ∃ C > (0 : ℝ), ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 →
    (D.chart a).γ t ∈ D.Xo → (D.lam1 ((D.chart a).γ t))⁻¹ ^ 2 ≤ C * (D.chart a).logR t

def ULamOne.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ z ∈ D.Xo, D.cuspU z ≤ ((Fintype.card Ψ * (D.N - D.j) : ℕ) : ℝ) *
    (2 * Real.posLog (D.lam1 z)⁻¹ +
      Real.log (2 * ((Fintype.card Ψ * (D.N - D.j) : ℕ) : ℝ) * rootDiscr Em))

def PhiHomLog.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ A0 : HermLine ι, A0.a = D.mu.aMu → IsSmoothHerm A0 →
    ∀ a, ∃ C > (0 : ℝ), ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 →
      (D.chart a).γ t ∈ D.Xo →
        |phMu D.mu ((D.chart a).γ t) - Real.log (A0.h ((D.chart a).γ t))| ≤
          C * Real.log ((D.chart a).logR t)

def ULogBound.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ A0 : HermLine ι, A0.a = D.mu.aMu → IsSmoothHerm A0 →
    ∀ a, ∃ C > (0 : ℝ), ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 →
      (D.chart a).γ t ∈ D.Xo →
        D.cuspU ((D.chart a).γ t) ≤ C * Real.log ((D.chart a).logR t) ∧
        |phMu D.mu ((D.chart a).γ t) + D.cuspU ((D.chart a).γ t) - Real.log (A0.h ((D.chart a).γ t))| ≤
          C * Real.log ((D.chart a).logR t)

theorem exp_one_le_logR {P : Ideal (MRing ι)} {n : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)}
    (χ : SncChart P n Bd) {t : Fin n → ℂ} (ht : ‖t‖ ≤ 1 / 2) : Real.exp 1 ≤ χ.logR t := by
  unfold SncChart.logR
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => ?_)
  split_ifs
  · have h1 : ‖t i‖ ≤ 1 := (norm_le_pi_norm t i).trans (ht.trans (by norm_num))
    rw [one_div, Real.log_inv, Real.log_pow]
    have := Real.log_nonpos (norm_nonneg (t i)) h1
    push_cast
    linarith
  · exact le_rfl

theorem one_le_log_logR {P : Ideal (MRing ι)} {n : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)}
    (χ : SncChart P n Bd) {t : Fin n → ℂ} (ht : ‖t‖ ≤ 1 / 2) : 1 ≤ Real.log (χ.logR t) := by
  have h := exp_one_le_logR χ ht
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (χ.logR t) := Real.log_le_log (Real.exp_pos 1) h

theorem posLog_le_of_sq_le {y C r : ℝ} (hC : 0 < C) (hr : 1 ≤ r) (h : y ^ 2 ≤ C * r) :
    Real.posLog y ≤ (|Real.log C| + Real.log r) / 2 := by
  have hr0 : 0 ≤ Real.log r := Real.log_nonneg hr
  have hC' : Real.log C ≤ |Real.log C| := le_abs_self _
  have hCa : 0 ≤ |Real.log C| := abs_nonneg _
  unfold Real.posLog
  refine max_le (by linarith) ?_
  rcases eq_or_ne y 0 with hy | hy
  · rw [hy, Real.log_zero]
    linarith
  · have hy2 : 0 < y ^ 2 := by positivity
    have h2 : Real.log (y ^ 2) ≤ Real.log (C * r) := Real.log_le_log hy2 h
    rw [Real.log_pow, Real.log_mul hC.ne' (by linarith)] at h2
    push_cast at h2
    linarith

theorem FullerData.cuspU_nonneg (D : FullerData II Ψ K ι Ω E Em) (z : (Σ k, ι k) → ℂ) : 0 ≤ D.cuspU z :=
  le_max_left _ _

theorem ULogBound.proof (D : FullerData II Ψ K ι Ω E Em) (hlam : LamOneChart.Statement D)
    (hU : ULamOne.Statement D) (hphi : PhiHomLog.Statement D) : ULogBound.Statement D := by
  intro A0 hA0 hsm a
  obtain ⟨C1, hC1, h1⟩ := hlam a
  obtain ⟨C2, hC2, h2⟩ := hphi A0 hA0 hsm a
  set fj : ℝ := ((Fintype.card Ψ * (D.N - D.j) : ℕ) : ℝ) with hfj
  set c3 : ℝ := Real.log (2 * fj * rootDiscr Em) with hc3
  have hfj0 : 0 ≤ fj := Nat.cast_nonneg _
  set Cu : ℝ := fj * (|Real.log C1| + 1 + |c3|) with hCu
  have hCu0 : 0 ≤ Cu := mul_nonneg hfj0 (by positivity)
  refine ⟨Cu + C2, by linarith, fun t ht hz => ?_⟩
  set L : ℝ := Real.log ((D.chart a).logR t) with hLdef
  have hL : 1 ≤ L := one_le_log_logR (D.chart a) ht
  have hr1 : 1 ≤ (D.chart a).logR t :=
    le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (exp_one_le_logR (D.chart a) ht)
  have hp : Real.posLog (D.lam1 ((D.chart a).γ t))⁻¹ ≤ (|Real.log C1| + L) / 2 :=
    posLog_le_of_sq_le hC1 hr1 (h1 t ht hz)
  have hUb := hU _ hz
  have hc3a : c3 ≤ |c3| := le_abs_self _
  have hUL : D.cuspU ((D.chart a).γ t) ≤ Cu * L := by
    have step1 : D.cuspU ((D.chart a).γ t) ≤ fj * (|Real.log C1| + L + |c3|) :=
      hUb.trans (mul_le_mul_of_nonneg_left (by linarith) hfj0)
    have step2 : |Real.log C1| + L + |c3| ≤ (|Real.log C1| + 1 + |c3|) * L := by
      nlinarith [abs_nonneg (Real.log C1), abs_nonneg c3]
    calc D.cuspU ((D.chart a).γ t) ≤ fj * (|Real.log C1| + L + |c3|) := step1
      _ ≤ fj * ((|Real.log C1| + 1 + |c3|) * L) := mul_le_mul_of_nonneg_left step2 hfj0
      _ = Cu * L := by rw [hCu]; ring
  have hphiL := h2 t ht hz
  have hU0 := D.cuspU_nonneg ((D.chart a).γ t)
  have hLpos : 0 ≤ L := by linarith
  have hC2L : 0 ≤ C2 * L := mul_nonneg hC2.le hLpos
  refine ⟨by nlinarith, ?_⟩
  rw [abs_le] at hphiL ⊢
  constructor <;> nlinarith

end GroundTheory.Heights₂.Heights.NineStatements
