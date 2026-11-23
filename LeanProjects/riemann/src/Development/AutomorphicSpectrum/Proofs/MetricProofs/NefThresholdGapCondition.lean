import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold

theorem ent_of_lt {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) {i : ℕ} (h : i < N) :
    GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i = mu τ ⟨i, h⟩ := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.ent
  rw [dif_pos h]

theorem abs_le_norm {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) (i : Fin N) :
    |mu τ i| ≤ ‖mu‖ := by
  have h1 : ‖mu τ i‖ ≤ ‖mu τ‖ := norm_le_pi_norm (mu τ) i
  have h2 : ‖mu τ‖ ≤ ‖mu‖ := norm_le_pi_norm mu τ
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h2

theorem gapCond_of_threshold {T : Type} [Fintype T] {N j p : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (hp : 2 < p) (hj : 1 ≤ j) (hjN : j < N) (hd : GlobalTheory.CompanionTheory.Ar.Top.Dominant mu)
    (ht : GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu) :
    GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.NefThreshold GlobalTheory.CompanionTheory.Ar.Top.gap at ht
  unfold GlobalTheory.CompanionTheory.Ar.Top.Dominant at hd
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold GapCond
  refine ⟨?_, ‖mu‖, 4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2), ?_, ?_, ?_⟩
  · intro τ i hi hiN
    have h1 : i < N := by omega
    have h0 : i - 1 < N := by omega
    simp only [Nat.add_sub_cancel]
    rw [ent_of_lt mu τ h1, ent_of_lt mu τ h0]
    exact hd τ ⟨i - 1, h0⟩ ⟨i, h1⟩ (Fin.mk_le_mk.2 (by omega))
  · intro τ i hi hiN
    have h0 : i - 1 < N := by omega
    simp only
    rw [ent_of_lt mu τ h0]
    exact abs_le_norm mu τ _
  · intro τ
    simp only [Nat.add_sub_cancel]
    rw [div_le_iff₀ hp']
    linarith [ht τ, mul_comm ((p : ℝ) - 2) (GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (j - 1) - GlobalTheory.CompanionTheory.Ar.Top.ent mu τ j)]
  · have e : ((p : ℝ) - 2) * (4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2)) = 4 * (Fintype.card T) * ‖mu‖ := by
      field_simp
    exact e.ge

theorem lmuNum_eq_sum {T : Type} [Fintype T] {N j : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ) (hjN : j < N)
    (hx : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i)
    (hy : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) :
    lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  classical
  unfold lmuNum
  set xx : T → ℕ → ℝ := fun τ i => if h : i < N then x (τ, ⟨i, h⟩) else 0 with hxx
  have hrow : ∀ τ, ∑ i : Fin N, -mu τ i * x (τ, i) =
      ∑ i ∈ Finset.range N, -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i := by
    intro τ
    rw [← Fin.sum_univ_eq_sum_range (fun i => -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i) N]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hxx, dif_pos i.isLt, ent_of_lt mu τ i.isLt]
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hrow τ, ← Finset.sum_range_add_sum_Ico _ hjN.le, Finset.sum_Ico_eq_sum_range, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_range.1 hi
    have hiN : i < N := by omega
    have hx' := hx τ ⟨i, hiN⟩ hij
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hx']
    ring
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmj : m < N - j := Finset.mem_range.1 hm
    have hiN : j + m < N := by omega
    have hy' := hy τ ⟨j + m, hiN⟩ (by simp)
    have e1 : N - 1 - (j + m) + 1 = N - j - m := by omega
    have e2 : N - 1 - (j + m) = N - j - m - 1 := by omega
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hy']
    rw [e1, e2]
    ring

theorem gapCond_and_lmuNum : ∀ (T : Type) [Fintype T] (N j p : ℕ) (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ), 2 < p → 1 ≤ j → j < N → GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu → (∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i) → (∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) → GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) ∧ lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  intro T _ N j p mu x w l hp hj hjN hd ht hx hy
  exact ⟨gapCond_of_threshold mu hp hj hjN hd ht, lmuNum_eq_sum mu x w l hjN hx hy⟩

end GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold
