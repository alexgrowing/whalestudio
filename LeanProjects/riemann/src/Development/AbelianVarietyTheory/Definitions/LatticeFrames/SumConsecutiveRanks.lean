import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PsiGeOn

noncomputable section

namespace GlobalTheory.Core.AtG

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable (D : D7) (EX : ErrX D) (u : D.what₂.Word)

def vDeg (i : Fin 2) (w : D.what₂.places.Pl) : ℝ := ∑ j ∈ Finset.Icc 1 D.R.m, vNN EX i u j w

def errF (D : D7) : ℝ := (D.R.f : ℝ) * D.R.m * (D.R.N D.R.m : ℝ) ^ 2

def errA (D : D7) : ℝ := errF D + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ)

def Big : Prop :=
  ∀ i : Fin 2, 2 * D.R.f * D.R.N D.R.m + 1 < D.host.g i ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, (∑ τ : D.what₂.Tau, nuAbs D u j τ) + 1 < (D.host.g i : ℝ)

def ColA : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errF D)

def PsiA : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    Int.PsiGeOn D u (DV.MramL D u) w ((D.what₂.places.ramIdx w : ℝ) * (-vDeg D EX u i w - errA D))

def PerA : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    Int.PerGeOn D u (DV.MramL D u) w ((D.what₂.places.ramIdx w : ℝ) * (-vDeg D EX u i w - errA D))

def DegExact : Prop :=
  ∀ j ∈ Finset.Icc 1 D.R.m, ∀ τ : D.what₂.Tau,
    nuAbs D u j τ =
      (∑ a : Fin D.R.k, (((D.hcW u τ).u a : ℝ) - ((D.R.k : ℝ) + 1 - 2 * ((a : ℝ) + 1)) / 2)) +
        (D.R.k : ℝ) * (wj D j τ - (D.R.k : ℝ) / 2 - (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) / 2) +
        ((D.R.t : ℝ) + 1) * ∑ i ∈ Finset.Ico 1 j, (wj D j τ - wj D i τ - ((j : ℝ) - i) * ((D.R.t : ℝ) + 1))

def UnitSum : Prop :=
  ∀ (i : Fin 2), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ S : Finset D.what₂.places.Pl,
    (∀ w, w ∈ S ↔ D.what₂.places.resChar w = D.host.g i) →
    ∑ w ∈ S, 2 * lw D.what₂.LL (D.plEq w) * ((D.what₂.places.ramIdx w : ℝ) * vNN EX i u j w) =
      (∑ τ : D.what₂.Tau, nuAbs D u j τ) * Real.log (D.host.g i : ℝ)

def DegLe (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ Finset.Icc 1 D.R.m,
    (∑ τ : D.what₂.Tau, nuAbs D u j τ) ≤ (∑ t : D.host.TT, (L.aT t : ℝ)) + (D.R.k : ℝ) * (∑ τ : D.what₂.Tau, wj D j τ) +
      C * (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * (L.etaSz + D.R.t))

theorem errF_le_errA (D : D7) : 0 ≤ errF D ∧ errF D ≤ errA D := by
  unfold errA errF
  constructor
  · positivity
  · have : 0 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) := by positivity
    linarith

def errStep (D : D7) : ℝ :=
  ∑ j ∈ Finset.range D.R.m, ((D.R.f : ℝ) * (D.R.N j : ℝ) * (D.R.N (j + 1) : ℝ) +
    2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ))

def ColStep : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errStep D)

def ColCoarse : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    ∀ x ∈ ((D.fm u).lat 0).L, Int.ColGe D u w x (-vDeg D EX u i w - errA D)

theorem sum_consecutive_ranks (k T : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (k + j * T) * (k + (j + 1) * T) =
      n * k ^ 2 + n ^ 2 * k * T + (n ^ 3 - n) / 3 * T ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem errStep_le_errF (D : D7) : errStep D ≤ errF D := by
  unfold errStep errF
  have h := sum_consecutive_ranks (D.R.k : ℝ) ((D.R.t : ℝ) + 1) D.R.m
  have e : ∑ j ∈ Finset.range D.R.m, (D.R.f : ℝ) * (D.R.N j : ℝ) * (D.R.N (j + 1) : ℝ) =
      (D.R.f : ℝ) * ∑ j ∈ Finset.range D.R.m,
        ((D.R.k : ℝ) + j * ((D.R.t : ℝ) + 1)) * ((D.R.k : ℝ) + (j + 1) * ((D.R.t : ℝ) + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Ranks.N]; push_cast; ring
  rw [Finset.sum_add_distrib, e, h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Ranks.N]
  push_cast
  have ht : 3 * (D.R.m : ℝ) ≤ (D.R.t : ℝ) + 1 := by
    have := D.R.three_m_lt_t
    have : 3 * D.R.m ≤ D.R.t + 1 := by omega
    exact_mod_cast this
  generalize (D.R.t : ℝ) + 1 = T at *
  have hm : (0 : ℝ) ≤ D.R.m := by positivity
  have hk : (0 : ℝ) ≤ D.R.k := by positivity
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.k : ℝ) = k at *
  generalize (D.R.f : ℝ) = f at *
  obtain ⟨s, rfl⟩ : ∃ s, T = 3 * m + s := ⟨T - 3 * m, by ring⟩
  have hs : 0 ≤ s := by linarith
  have : f * m * (k + m * (3 * m + s)) ^ 2 - (f * (m * k ^ 2 + m ^ 2 * k * (3 * m + s) + (m ^ 3 - m) / 3 * (3 * m + s) ^ 2) +
      m * (2 * f * m ^ 2 * (k + m * (3 * m + s)))) =
      f * (m ^ 2 * k * (m + s) + 2 / 3 * m ^ 3 * (3 * m + s) * s + m / 3 * (3 * m + s) ^ 2) := by ring
  have h2 : 0 ≤ f * (m ^ 2 * k * (m + s) + 2 / 3 * m ^ 3 * (3 * m + s) * s + m / 3 * (3 * m + s) ^ 2) := by positivity
  linarith

theorem colGe_of_le (w : D.what₂.places.Pl) (x : ((D.fm u).lat 0).V) {s t : ℝ} (hst : s ≤ t)
    (h : Int.ColGe D u w x t) : Int.ColGe D u w x s := by
  obtain ⟨y, hy, a, z, hz, hya, ha⟩ := h
  exact ⟨y, hy, a, z, hz, hya, ha.imp id fun ha => le_trans (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg _)) ha⟩

theorem colA_of_colStep (h : ColStep D EX u) : ColA D EX u := fun i w hw x hx =>
  colGe_of_le D u w x (by linarith [errStep_le_errF D]) (h i w hw x hx)

theorem colCoarse_of_colA (h : ColA D EX u) : ColCoarse D EX u := fun i w hw x hx =>
  colGe_of_le D u w x (by linarith [(errF_le_errA D).2]) (h i w hw x hx)

example : ∑ j ∈ Finset.range 2, ((5 + j * 8) * (5 + (j + 1) * 8) + 2 * 2 ^ 2 * 21) = 674 ∧ 2 * 21 ^ 2 = 882 := by decide

example (D : D7) : errA D - errF D = 2 * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) := by unfold errA; ring

end GlobalTheory.Core.AtG
