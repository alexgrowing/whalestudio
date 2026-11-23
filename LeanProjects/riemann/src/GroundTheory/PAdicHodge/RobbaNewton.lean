import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

namespace Laurent

variable {a b : ℤ → K} {ρ : ℝ}

def slopeMult (a : ℤ → K) (ρ : ℝ) : ℤ := highIndex a ρ - lowIndex a ρ

theorem zpow_rpow_comm {x : ℝ} (hx : 0 < x) (n : ℤ) (s : ℝ) : (x ^ s) ^ n = (x ^ n) ^ s := by
  rw [← Real.rpow_intCast, ← Real.rpow_intCast x n, ← Real.rpow_mul hx.le,
    ← Real.rpow_mul hx.le, mul_comm]

theorem weight_interp {ρ₁ ρ₂ t : ℝ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂) (n : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    x * (ρ₁ ^ (1 - t) * ρ₂ ^ t) ^ n = (x * ρ₁ ^ n) ^ (1 - t) * (x * ρ₂ ^ n) ^ t := by
  rw [mul_zpow, zpow_rpow_comm h1, zpow_rpow_comm h2, Real.mul_rpow hx (by positivity),
    Real.mul_rpow hx (by positivity)]
  have : x = x ^ (1 - t) * x ^ t := by
    rw [← Real.rpow_add' hx (by norm_num), sub_add_cancel, Real.rpow_one]
  conv_lhs => rw [this]
  ring

theorem gaussNorm_interp_le {ρ₁ ρ₂ t : ℝ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂) (hc1 : ConvergesAt a ρ₁)
    (hc2 : ConvergesAt a ρ₂) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gaussNorm a (ρ₁ ^ (1 - t) * ρ₂ ^ t) ≤ gaussNorm a ρ₁ ^ (1 - t) * gaussNorm a ρ₂ ^ t :=
  gaussNorm_le fun n => by
    rw [weight_interp h1 h2 n (norm_nonneg _)]
    exact mul_le_mul (Real.rpow_le_rpow (by positivity) (hc1.le_gaussNorm n) (by linarith))
      (Real.rpow_le_rpow (by positivity) (hc2.le_gaussNorm n) ht0) (by positivity)
      (Real.rpow_nonneg (gaussNorm_nonneg h1) _)

theorem gaussNorm_le_max {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (hle1 : ρ₁ ≤ ρ) (hle2 : ρ ≤ ρ₂)
    (hc1 : ConvergesAt a ρ₁) (hc2 : ConvergesAt a ρ₂) :
    gaussNorm a ρ ≤ max (gaussNorm a ρ₁) (gaussNorm a ρ₂) := by
  have hρ : 0 < ρ := h1.trans_le hle1
  refine gaussNorm_le fun n => ?_
  rcases le_total 0 n with hn | hn
  · exact ((mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hn hρ.le hle2) (norm_nonneg _)).trans
      (hc2.le_gaussNorm n)).trans (le_max_right _ _)
  · have h3 : ρ ^ n ≤ ρ₁ ^ n := by
      rw [show ρ ^ n = (ρ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
        show ρ₁ ^ n = (ρ₁ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (neg_nonneg.2 hn) h1.le hle1)
    exact ((mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans (hc1.le_gaussNorm n)).trans
      (le_max_left _ _)

end Laurent

namespace Laurent

variable {a : ℤ → K} {α β : ℝ}

theorem lowIndex_mono {ρ ρ' : ℝ} (hρ : 0 < ρ) (hle : ρ ≤ ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) : lowIndex a ρ ≤ lowIndex a ρ' := by
  rcases hle.lt_or_eq with hlt | rfl
  · exact (lowIndex_le_highIndex hρ h ha).trans (highIndex_le_lowIndex hρ hlt h h' ha)
  · exact le_rfl

theorem highIndex_mono {ρ ρ' : ℝ} (hρ : 0 < ρ) (hle : ρ ≤ ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) : highIndex a ρ ≤ highIndex a ρ' := by
  rcases hle.lt_or_eq with hlt | rfl
  · exact (highIndex_le_lowIndex hρ hlt h h' ha).trans (lowIndex_le_highIndex (hρ.trans hlt) h' ha)
  · exact le_rfl

theorem exists_break (hα : 0 < α) (hαβ : α ≤ β) (hA : ConvergesAt a α) (hB : ConvergesAt a β)
    (ha : a ≠ 0) {n : ℤ} (hn1 : lowIndex a α ≤ n) (hn2 : n < highIndex a β) :
    ∃ σ ∈ Set.Icc α β, lowIndex a σ ≤ n ∧ n < highIndex a σ := by
  have hconv : ∀ σ ∈ Set.Icc α β, ConvergesAt a σ := fun σ hσ =>
    hA.of_le_of_le hB hα hσ.1 hσ.2
  have hpos : ∀ σ ∈ Set.Icc α β, 0 < σ := fun σ hσ => hα.trans_le hσ.1
  have hβ : 0 < β := hα.trans_le hαβ
  by_cases h1 : n < highIndex a α
  · exact ⟨α, ⟨le_rfl, hαβ⟩, hn1, h1⟩
  by_cases h2 : lowIndex a β ≤ n
  · exact ⟨β, ⟨hαβ, le_rfl⟩, h2, hn2⟩
  push_neg at h1 h2
  have hLα := lowIndex_le_highIndex hα hA ha
  have hLβ := lowIndex_le_highIndex hβ hB ha
  have hαβ' : α < β := by
    rcases hαβ.lt_or_eq with h | h
    · exact h
    · subst h; omega
  set C := Finset.Icc (lowIndex a α) (highIndex a β)
  set C1 := C.filter (· ≤ n)
  set C2 := C.filter (n < ·)
  have hC1 : highIndex a α ∈ C1 := by simp only [C1, C, Finset.mem_filter, Finset.mem_Icc]; omega
  have hC2 : lowIndex a β ∈ C2 := by simp only [C2, C, Finset.mem_filter, Finset.mem_Icc]; omega
  have ne1 : C1.Nonempty := ⟨_, hC1⟩
  have ne2 : C2.Nonempty := ⟨_, hC2⟩
  set A : ℝ → ℝ := fun σ => C1.sup' ne1 fun k => ‖a k‖ * σ ^ k
  set B : ℝ → ℝ := fun σ => C2.sup' ne2 fun k => ‖a k‖ * σ ^ k
  have hw : ∀ k : ℤ, ContinuousOn (fun σ : ℝ => ‖a k‖ * σ ^ k) (Set.Icc α β) := fun k =>
    continuousOn_const.mul ((continuousOn_zpow₀ k).mono fun σ hσ =>
      Set.mem_compl_singleton_iff.2 (hpos σ hσ).ne')
  have hcont : ContinuousOn (fun σ => A σ - B σ) (Set.Icc α β) :=
    (ContinuousOn.finset_sup'_apply ne1 fun k _ => hw k).sub
      (ContinuousOn.finset_sup'_apply ne2 fun k _ => hw k)
  have hAle : ∀ σ ∈ Set.Icc α β, A σ ≤ gaussNorm a σ := fun σ hσ =>
    Finset.sup'_le _ _ fun k _ => (hconv σ hσ).le_gaussNorm k
  have hBle : ∀ σ ∈ Set.Icc α β, B σ ≤ gaussNorm a σ := fun σ hσ =>
    Finset.sup'_le _ _ fun k _ => (hconv σ hσ).le_gaussNorm k
  have hgα : 0 < A α - B α := by
    have e1 : gaussNorm a α ≤ A α := by
      rw [← show ‖a (highIndex a α)‖ * α ^ highIndex a α = gaussNorm a α from
        highIndex_mem hα hA ha]
      exact Finset.le_sup' (fun k => ‖a k‖ * α ^ k) hC1
    have e2 : B α < gaussNorm a α := (Finset.sup'_lt_iff _).2 fun k hk => by
      simp only [C2, Finset.mem_filter] at hk
      exact weight_lt_of_highIndex_lt hα hA ha (by omega)
    linarith
  have hgβ : A β - B β < 0 := by
    have e1 : gaussNorm a β ≤ B β := by
      rw [← show ‖a (lowIndex a β)‖ * β ^ lowIndex a β = gaussNorm a β from
        lowIndex_mem hβ hB ha]
      exact Finset.le_sup' (fun k => ‖a k‖ * β ^ k) hC2
    have e2 : A β < gaussNorm a β := (Finset.sup'_lt_iff _).2 fun k hk => by
      simp only [C1, Finset.mem_filter] at hk
      exact weight_lt_of_lt_lowIndex hβ hB ha (by omega)
    linarith
  obtain ⟨σ, hσ, hgσ⟩ := intermediate_value_Icc' hαβ hcont ⟨hgβ.le, hgα.le⟩
  simp only at hgσ
  have hσα : α < σ := lt_of_le_of_ne hσ.1 fun h => by subst h; linarith
  have hσβ : σ < β := lt_of_le_of_ne hσ.2 fun h => by subst h; linarith
  have hσ0 := hpos σ hσ
  have hcσ := hconv σ hσ
  have i1 := highIndex_le_lowIndex hα hσα hA hcσ ha
  have i2 := highIndex_le_lowIndex hσ0 hσβ hcσ hB ha
  have i3 := lowIndex_le_highIndex hσ0 hcσ ha
  have hLmem := lowIndex_mem hσ0 hcσ ha
  have hgauss : gaussNorm a σ ≤ max (A σ) (B σ) := by
    rw [← show ‖a (lowIndex a σ)‖ * σ ^ lowIndex a σ = gaussNorm a σ from hLmem]
    by_cases hk : lowIndex a σ ≤ n
    · exact (Finset.le_sup' (fun k => ‖a k‖ * σ ^ k) (s := C1)
        (by simp only [C1, C, Finset.mem_filter, Finset.mem_Icc]; omega)).trans (le_max_left _ _)
    · exact (Finset.le_sup' (fun k => ‖a k‖ * σ ^ k) (s := C2)
        (by simp only [C2, C, Finset.mem_filter, Finset.mem_Icc]; omega)).trans (le_max_right _ _)
  have hAσ : A σ = gaussNorm a σ := by
    have := hAle σ hσ; have := hBle σ hσ
    rcases le_total (A σ) (B σ) with h | h
    · rw [max_eq_right h] at hgauss; linarith
    · rw [max_eq_left h] at hgauss; linarith
  have hBσ : B σ = gaussNorm a σ := by linarith
  obtain ⟨k1, hk1, hk1e⟩ := Finset.exists_mem_eq_sup' ne1 fun k => ‖a k‖ * σ ^ k
  obtain ⟨k2, hk2, hk2e⟩ := Finset.exists_mem_eq_sup' ne2 fun k => ‖a k‖ * σ ^ k
  have d1 : k1 ∈ domSet a σ := by
    show ‖a k1‖ * σ ^ k1 = gaussNorm a σ
    rw [← hk1e]; exact hAσ
  have d2 : k2 ∈ domSet a σ := by
    show ‖a k2‖ * σ ^ k2 = gaussNorm a σ
    rw [← hk2e]; exact hBσ
  simp only [C1, C2, Finset.mem_filter] at hk1 hk2
  exact ⟨σ, hσ, (lowIndex_le hσ0 hcσ ha d1).trans hk1.2,
    lt_of_lt_of_le hk2.2 (le_highIndex hσ0 hcσ ha d2)⟩

def breaks (a : ℤ → K) (α β : ℝ) : Set ℝ :=
  {ρ | ρ ∈ Set.Icc α β ∧ lowIndex a ρ < highIndex a ρ}

section Finite

variable (hα : 0 < α) (hαβ : α ≤ β) (hA : ConvergesAt a α) (hB : ConvergesAt a β) (ha : a ≠ 0)
include hα hαβ hA hB ha

theorem mem_Icc_indices {ρ : ℝ} (hρ : ρ ∈ Set.Icc α β) :
    lowIndex a α ≤ lowIndex a ρ ∧ highIndex a ρ ≤ highIndex a β := by
  have hc := hA.of_le_of_le hB hα hρ.1 hρ.2
  exact ⟨lowIndex_mono hα hρ.1 hA hc ha, highIndex_mono (hα.trans_le hρ.1) hρ.2 hc hB ha⟩

theorem breaks_finite : (breaks a α β).Finite := by
  refine Set.Finite.of_finite_image (f := fun ρ => lowIndex a ρ)
    ((Set.finite_Icc (lowIndex a α) (highIndex a β)).subset ?_) ?_
  · rintro _ ⟨ρ, hρ, rfl⟩
    have := mem_Icc_indices hα hαβ hA hB ha hρ.1
    exact ⟨this.1, hρ.2.le.trans this.2⟩
  · intro ρ hρ ρ' hρ' he
    simp only at he
    have hc := hA.of_le_of_le hB hα hρ.1.1 hρ.1.2
    have hc' := hA.of_le_of_le hB hα hρ'.1.1 hρ'.1.2
    rcases lt_trichotomy ρ ρ' with h | h | h
    · have := highIndex_le_lowIndex (hα.trans_le hρ.1.1) h hc hc' ha
      have := hρ.2
      omega
    · exact h
    · have := highIndex_le_lowIndex (hα.trans_le hρ'.1.1) h hc' hc ha
      have := hρ'.2
      omega

theorem sum_slopeMult_breaks :
    ∑ ρ ∈ (breaks_finite hα hαβ hA hB ha).toFinset, slopeMult a ρ =
      highIndex a β - lowIndex a α := by
  classical
  set s := (breaks_finite hα hαβ hA hB ha).toFinset
  set I : ℝ → Finset ℤ := fun ρ => Finset.Ico (lowIndex a ρ) (highIndex a ρ)
  have hmem : ∀ ρ, ρ ∈ s ↔ ρ ∈ breaks a α β := fun ρ => Set.Finite.mem_toFinset _
  have hdisj : (s : Set ℝ).PairwiseDisjoint I := by
    intro ρ hρ ρ' hρ' hne
    rw [Finset.mem_coe, hmem] at hρ hρ'
    have hc := hA.of_le_of_le hB hα hρ.1.1 hρ.1.2
    have hc' := hA.of_le_of_le hB hα hρ'.1.1 hρ'.1.2
    show Disjoint (I ρ) (I ρ')
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [I, Finset.mem_Ico] at hk hk'
    rcases lt_or_gt_of_ne hne with h | h
    · have := highIndex_le_lowIndex (hα.trans_le hρ.1.1) h hc hc' ha
      omega
    · have := highIndex_le_lowIndex (hα.trans_le hρ'.1.1) h hc' hc ha
      omega
  have hLH : lowIndex a α ≤ highIndex a β :=
    (lowIndex_le_highIndex hα hA ha).trans (highIndex_mono hα hαβ hA hB ha)
  have hunion : s.biUnion I = Finset.Ico (lowIndex a α) (highIndex a β) := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_Ico, hmem, I]
    constructor
    · rintro ⟨ρ, hρ, hk1, hk2⟩
      have := mem_Icc_indices hα hαβ hA hB ha hρ.1
      omega
    · rintro ⟨hk1, hk2⟩
      obtain ⟨σ, hσ, h1, h2⟩ := exists_break hα hαβ hA hB ha hk1 hk2
      exact ⟨σ, ⟨hσ, by omega⟩, h1, h2⟩
  have hcard := Finset.card_biUnion hdisj
  rw [hunion, Int.card_Ico] at hcard
  have : ∑ ρ ∈ s, slopeMult a ρ = ∑ ρ ∈ s, ((I ρ).card : ℤ) := Finset.sum_congr rfl fun ρ hρ => by
    rw [hmem] at hρ
    simp only [I, Int.card_Ico, slopeMult]
    have := hρ.2
    omega
  rw [this, ← Nat.cast_sum, ← hcard]
  omega

end Finite

end Laurent

namespace Robba

variable [CompleteSpace K]

end Robba

end GroundTheory.PAdicHodge
