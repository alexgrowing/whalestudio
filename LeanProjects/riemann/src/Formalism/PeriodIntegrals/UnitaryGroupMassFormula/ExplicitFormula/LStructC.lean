import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructB

noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

lemma isCompact_rect (x₀ x₁ y₀ y₁ : ℝ) : IsCompact (rect x₀ x₁ y₀ y₁) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma mem_rect {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by
  simp only [rect, Complex.mem_reProdIm, Set.mem_Icc]

variable {N : ℕ} [NeZero N]

def Lent (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  open Classical in if χ = 1 then LFunctionTrivChar₁ N else LFunction χ

lemma differentiable_Lent (χ : DirichletCharacter ℂ N) : Differentiable ℂ (Lent χ) := by
  unfold Lent
  split_ifs with h
  · exact differentiable_LFunctionTrivChar₁ N
  · exact differentiable_LFunction h

lemma Lent_of_ne {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) : Lent χ = LFunction χ := by
  unfold Lent
  rw [if_neg h]

lemma Lent_one_apply {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = (s - 1) * LFunction χ s := by
  subst h
  unfold Lent
  rw [if_pos rfl]
  first
    | (rw [LFunctionTrivChar₁, Function.update_of_ne hs]; rfl)
    | (simp [LFunctionTrivChar₁, Function.update_of_ne hs])
    | (simp [LFunctionTrivChar₁, hs])

lemma Lent_two_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 2 ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have hL : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inr h2) (by norm_num)
  by_cases h : χ = 1
  · rw [Lent_one_apply h h2]
    exact mul_ne_zero (sub_ne_zero.mpr h2) hL
  · rw [Lent_of_ne h]
    exact hL

lemma Lent_one_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 1 ≠ 0 := by
  by_cases h : χ = 1
  · unfold Lent
    rw [if_pos h]
    exact LFunctionTrivChar₁_apply_one_ne_zero N
  · rw [Lent_of_ne h]
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h) (by simp)

lemma Lent_eq_zero_iff (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = 0 ↔ LFunction χ s = 0 := by
  by_cases h : χ = 1
  · rw [Lent_one_apply h hs, mul_eq_zero]
    simp [sub_eq_zero, hs]
  · rw [Lent_of_ne h]

lemma Lent_eventuallyEq {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ =ᶠ[𝓝 s] (fun z => z - 1) * LFunction χ := by
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  rw [Lent_one_apply h hz]
  rfl

lemma order_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt (Lent χ) s = analyticOrderNatAt (LFunction χ) s := by
  by_cases h : χ = 1
  · have hL : AnalyticAt ℂ (LFunction χ) s := by
      apply DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      · intro z hz
        exact (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
      · exact isOpen_ne.mem_nhds hs
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
      h1.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs)
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr (Lent_eventuallyEq h hs), analyticOrderAt_mul h1 hL, h0, zero_add]
  · rw [Lent_of_ne h]

lemma logDeriv_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) (h0 : LFunction χ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (Lent χ) s - del1 χ / (s - 1) := by
  by_cases h : χ = 1
  · have hd : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s (Or.inl hs)
    have he := Lent_eventuallyEq h hs
    have h1 : logDeriv (Lent χ) s = logDeriv (fun z => (z - 1) * LFunction χ z) s := by
      unfold logDeriv
      simp only [Pi.div_apply]
      rw [he.deriv_eq, he.eq_of_nhds]
      rfl
    have h2 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
      simp [logDeriv_apply]
    have hdz : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const (1 : ℂ)
    rw [h1, logDeriv_mul (f := fun z : ℂ => z - 1) (g := LFunction χ) s
      (sub_ne_zero.mpr hs) h0 hdz hd, h2]
    simp only [del1, if_pos h]
    ring
  · rw [Lent_of_ne h]
    simp [del1, h]

theorem zerosFinite : ZerosFinite := by
  intro N _ χ hχ T
  have h := finite_zeros_of_compact (differentiable_Lent χ) (Lent_two_ne_zero χ)
    (isCompact_rect 0 1 (-T) T)
  refine h.subset ?_
  intro ρ hρ
  obtain ⟨hre0, hre1, him, hL⟩ := hρ
  have h1 : ρ ≠ 1 := fun e => by rw [e] at hre1; simp at hre1
  refine ⟨mem_rect.mpr ⟨⟨hre0.le, hre1.le⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [neg_abs_le ρ.im]
  · linarith [le_abs_self ρ.im]
  · exact (Lent_eq_zero_iff χ h1).mpr hL

theorem regularPart : RegularPart := by
  intro N _ χ hχ x₁ T' hx₁ hT' hNO
  classical
  have hSfin : (ZerosBelow χ T').Finite := zerosFinite N χ hχ T'

  obtain ⟨E0, hE0⟩ : ∃ E0 : Finset ℂ, E0 = if χ.Even ∧ χ ≠ 1 then {0} else ∅ := ⟨_, rfl⟩
  have hE0mem : ∀ ρ, ρ ∈ E0 ↔ ρ = 0 ∧ χ.Even ∧ χ ≠ 1 := by
    intro ρ
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.mem_singleton]
      exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
    · rw [if_neg he]
      simp only [Finset.notMem_empty, false_iff]
      exact fun h => he h.2
  have hre1 : ∀ ρ ∈ ZerosBelow χ T', ρ ≠ 1 := by
    intro ρ hρ e
    have h := hρ.2.1
    rw [e] at h
    simp at h
  have hZ0 : ∀ ρ ∈ hSfin.toFinset ∪ E0, Lent χ ρ = 0 := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · have h' := hSfin.mem_toFinset.mp h
      exact (Lent_eq_zero_iff χ (hre1 ρ h')).mpr h'.2.2.2
    · obtain ⟨rfl, he, h1⟩ := (hE0mem ρ).mp h
      exact (Lent_eq_zero_iff χ zero_ne_one).mpr (mult_zero_of_even hχ he h1).1
  have hK : ∀ s ∈ rect (-1 / 2) x₁ (-T') T', Lent χ s = 0 → s ∈ hSfin.toFinset ∪ E0 := by
    intro s hs hz
    have hs1 : s ≠ 1 := fun e => Lent_one_ne_zero χ (e ▸ hz)
    have hL : LFunction χ s = 0 := (Lent_eq_zero_iff χ hs1).mp hz
    obtain ⟨⟨hsre0, hsre1⟩, him0, him1⟩ := mem_rect.mp hs
    rcases zeroLocus N χ hχ s (by linarith) hs1 hL with h | h | h
    · apply Finset.mem_union_left
      rw [hSfin.mem_toFinset]
      refine ⟨h.1, h.2, ?_, hL⟩
      have hle : |s.im| ≤ T' := abs_le.mpr ⟨him0, him1⟩
      exact lt_of_le_of_ne hle (hNO s h.1 h.2 hL)
    · exact Finset.mem_union_right _ ((hE0mem s).mpr h)
    · exfalso
      rw [h.1] at hsre0
      norm_num at hsre0
  have hf : AnalyticOnNhd ℂ (Lent χ) (rect (-1 / 2) x₁ (-T') T') := fun x _ =>
    (differentiable_Lent χ).analyticAt x
  have hfin : ∀ ρ ∈ rect (-1 / 2) x₁ (-T') T', analyticOrderAt (Lent χ) ρ ≠ ⊤ := fun ρ _ =>
    order_ne_top_of_entire (differentiable_Lent χ) (Lent_two_ne_zero χ) ρ
  obtain ⟨H, hH, hHeq⟩ := exists_regular_part hf (hSfin.toFinset ∪ E0) hZ0 hK hfin
  refine ⟨H, hH.differentiableOn, ?_⟩
  intro s hs hL0 hs1
  have hLe : Lent χ s ≠ 0 := fun e => hL0 ((Lent_eq_zero_iff χ hs1).mp e)
  have hdisj : Disjoint hSfin.toFinset E0 := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have h1' := (hSfin.mem_toFinset.mp h1).1
    rw [((hE0mem ρ).mp h2).1] at h1'
    simp at h1'
  have hS : ∑ ρ ∈ hSfin.toFinset, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) =
      ∑ ρ ∈ hSfin.toFinset, (mult χ ρ : ℂ) / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [order_Lent χ (hre1 ρ (hSfin.mem_toFinset.mp hρ))]
  have hE : ∑ ρ ∈ E0, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) = eps0 χ / s := by
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.sum_singleton, order_Lent χ zero_ne_one,
        (mult_zero_of_even hχ he.1 he.2).2]
      simp only [eps0, if_pos he]
      simp
    · rw [if_neg he]
      simp only [eps0, if_neg he]
      simp
  rw [logDeriv_Lent χ hs1 hL0, hHeq s hs hLe, Finset.sum_union hdisj,
    finsum_mem_eq_finite_toFinset_sum _ hSfin, hS, hE]
  ring

end PI.EF
