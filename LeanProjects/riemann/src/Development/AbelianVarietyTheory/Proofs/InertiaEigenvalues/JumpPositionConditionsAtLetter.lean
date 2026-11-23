import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntPts

noncomputable section

open Classical

namespace GlobalTheory.PositionData

theorem mnLo_le_zero' (Fl : Finset ℤ) : mnLo Fl ≤ 0 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem mnLo_le' (Fl : Finset ℤ) {z : ℤ} (hz : z ∈ Fl) : mnLo Fl ≤ z :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem hz)

theorem le_mxLo' (t : ℕ) (Fl : Finset ℤ) : (t : ℤ) - 1 ≤ mxLo t Fl :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem le_mxLo_of_mem (t : ℕ) (Fl : Finset ℤ) {z : ℤ} (hz : z ∈ Fl) : z ≤ mxLo t Fl :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem hz)

theorem mxLo_cases (t : ℕ) (Fl : Finset ℤ) : mxLo t Fl = (t : ℤ) - 1 ∨ mxLo t Fl ∈ Fl :=
  Finset.mem_insert.mp (Finset.max'_mem _ _)

theorem mnLo_cases (Fl : Finset ℤ) : mnLo Fl = 0 ∨ mnLo Fl ∈ Fl :=
  Finset.mem_insert.mp (Finset.min'_mem _ _)

theorem mnAll_le_zero' (Fl Fc : Finset ℤ) : mnAll Fl Fc ≤ 0 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem mnAll_le' (Fl Fc : Finset ℤ) {z : ℤ} (hz : z ∈ Fl ∪ Fc) : mnAll Fl Fc ≤ z :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem hz)

theorem le_mxAll' (t : ℕ) (Fl Fc : Finset ℤ) : (t : ℤ) - 1 ≤ mxAll t Fl Fc :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem le_mxAll_of_mem (t : ℕ) (Fl Fc : Finset ℤ) {z : ℤ} (hz : z ∈ Fl ∪ Fc) :
    z ≤ mxAll t Fl Fc :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem hz)

theorem far_from_block (z c σ : ℤ) (t : ℕ) (B : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ (t : ℤ) - 1)
    (hσ : (σ : ℝ) ≤ 2 * B) (hz : 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) :
    σ + 2 < |z - c| := by
  have hc0' : (0 : ℝ) ≤ c := by exact_mod_cast hc0
  have hc1' : (c : ℝ) ≤ (t : ℝ) - 1 := by exact_mod_cast hc1
  have key : (σ : ℝ) + 2 < |(z : ℝ) - c| := by
    rcases le_abs'.mp hz with h | h
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; linarith
  exact_mod_cast key

end GlobalTheory.PositionData

namespace GlobalTheory.PositionData

theorem position_conditions : ∀ (l t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ) (sgP σ : ℤ),
    1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    (∀ n : ℤ, W0 + (-η - 2 * (sgP : ℝ) - 3) ≤ (n : ℝ) → (n : ℝ) ≤ W0 + (S + η + η + 2 * (sgP : ℝ) + 4) →
      ¬ (l : ℤ) ∣ n) →
    (σ : ℝ) ≤ 2 * B → σ ≤ sgP → 2 * η + 8 * B + 7 < (l : ℝ) →
    (∀ u ∈ GlobalTheory.PositionData.US up Fl Fc, 1 ≤ u ∧ u ≤ (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - 1) ∧
    1 ≤ GlobalTheory.PositionData.wS up Fl Fc ∧
    (GlobalTheory.PositionData.wS up Fl Fc : ℤ) + t - 1 ≤ (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - 1 ∧
    (up = true → (GlobalTheory.PositionData.wS up Fl Fc : ℤ) + t - 1 ≤ GlobalTheory.PositionData.etaS t Fl) ∧
    (up = false → (GlobalTheory.PositionData.hS up t Fl Fc : ℤ) - GlobalTheory.PositionData.etaS t Fl ≤ GlobalTheory.PositionData.wS up Fl Fc) ∧
    (GlobalTheory.PositionData.etaS t Fl : ℤ) + 4 * σ + 6 < l ∧
    (∀ x ∈ Formalism.MainNotions.tableLineDegreeTwo.lows up (GlobalTheory.PositionData.hS up t Fl Fc) (GlobalTheory.PositionData.etaS t Fl) (GlobalTheory.PositionData.US up Fl Fc),
      ∀ y ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (GlobalTheory.PositionData.wS up Fl Fc) t, σ + 2 < |x - y|) ∧
    Formalism.WachCohomologyFacts.V2.ResidueAvoidance l up (GlobalTheory.PositionData.hS up t Fl Fc) (GlobalTheory.PositionData.etaS t Fl) σ (GlobalTheory.PositionData.US up Fl Fc) := by
  intro l t up Fl Fc η S B W0 sgP σ ht htη hB hS0 hFl hFc hW0 hn hσB hσs hl
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hσs' : (σ : ℝ) ≤ sgP := by exact_mod_cast hσs
  have hmx0 := le_mxLo' t Fl
  have hmn0 := mnLo_le_zero' Fl
  have hmx : (mxLo t Fl : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    rcases mxLo_cases t Fl with h | h
    · rw [h]; push_cast; linarith
    · have := (hFl _ h).1; rw [abs_le] at this; linarith
  have hmn : ((t : ℝ) - 1) / 2 - η ≤ (mnLo Fl : ℝ) := by
    rcases mnLo_cases Fl with h | h
    · rw [h]; push_cast; linarith
    · have := (hFl _ h).1; rw [abs_le] at this; linarith
  have hηS : (etaS t Fl : ℤ) = mxLo t Fl - mnLo Fl + 1 := by
    unfold etaS; rw [Int.toNat_of_nonneg]; omega

  have hfar : ∀ z ∈ Fl ∪ Fc, 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2| := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact (hFl z h).2
    · have := (hFc z h).1
      cases up
      · simp only [Bool.false_eq_true, if_false] at this
        rw [abs_sub_comm]; exact le_trans hW0 (le_trans this (le_abs_self _))
      · simp only [if_true] at this
        exact le_trans hW0 (le_trans this (le_abs_self _))
  have hT1 : (etaS t Fl : ℤ) + 4 * σ + 6 < l := by
    have : ((etaS t Fl : ℤ) : ℝ) + 4 * σ + 6 < l := by
      rw [hηS]; push_cast; linarith
    exact_mod_cast this
  have hT2 : ∀ x ∈ US up Fl Fc, ∀ y ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (wS up Fl Fc) t, σ + 2 < |x - y| := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
    rw [Formalism.WachCohomologyFacts.Top.GlobalTheory, Finset.mem_Icc] at hy
    have := far_from_block z (y - wS up Fl Fc) σ t B (by omega) (by omega) hσB
      (hfar z (Finset.mem_val.mp hz))
    have e : z + (wS up Fl Fc : ℤ) - y = z - (y - wS up Fl Fc) := by ring
    rw [e]; exact this
  have hT2' : ∀ x ∈ Formalism.MainNotions.tableLineDegreeTwo.lows up (hS up t Fl Fc) (etaS t Fl) (US up Fl Fc),
      ∀ y ∈ Formalism.WachCohomologyFacts.Top.GlobalTheory (wS up Fl Fc) t, σ + 2 < |x - y| := by
    intro x hx
    exact hT2 x (Multiset.mem_filter.mp hx).1
  cases up
  ·
    have hmA0 := mnAll_le_zero' Fl Fc
    have hw : (wS false Fl Fc : ℤ) = 1 - mnAll Fl Fc := by
      simp only [wS, Bool.false_eq_true, if_false]; rw [Int.toNat_of_nonneg]; omega
    have hh : (hS false t Fl Fc : ℤ) = mxLo t Fl + (1 - mnAll Fl Fc) + 1 := by
      simp only [hS, Bool.false_eq_true, if_false]; rw [Int.toNat_of_nonneg] <;> omega
    have hcl : ∀ z ∈ Fc, ((z : ℝ)) ≤ ((t : ℝ) - 1) / 2 - W0 ∧
        ((t : ℝ) - 1) / 2 - (W0 + S + η + 1) ≤ z := by
      intro z hz
      have := hFc z hz
      simp only [Bool.false_eq_true, if_false] at this
      constructor <;> linarith [this.1, this.2]
    refine ⟨?_, by omega, by omega, by simp, fun _ => by omega, hT1, hT2', ?_⟩
    · intro u hu
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hu
      have hz' := Finset.mem_val.mp hz
      have h1 := mnAll_le' Fl Fc hz'
      have h2 : z ≤ mxLo t Fl := by
        rcases Finset.mem_union.mp hz' with h | h
        · exact le_mxLo_of_mem t Fl h
        · have := (hcl z h).1
          have : (z : ℝ) < ((t : ℤ) - 1 : ℤ) := by push_cast; linarith
          have : z < (t : ℤ) - 1 := by exact_mod_cast this
          omega
      omega
    · intro x hx m hm1 hm2
      rcases Multiset.mem_filter.mp hx with ⟨hxU, hxW⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hxU
      have hz' := Finset.mem_val.mp hz
      simp only [Formalism.WachCohomologyFacts.V2.InWinN, Bool.false_eq_true, if_false] at hxW
      have hzc : z ∈ Fc := by
        rcases Finset.mem_union.mp hz' with h | h
        · exfalso; apply hxW
          have := mnLo_le' Fl h; have := le_mxLo_of_mem t Fl h
          constructor <;> omega
        · exact h
      simp only [Bool.false_eq_true, if_false]
      intro heq
      have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub m _ l).mp heq.symm
      rw [hηS] at hm2
      have e : (hS false t Fl Fc : ℤ) - (z + (wS false Fl Fc : ℤ)) = mxLo t Fl + 1 - z := by
        rw [hh, hw]; ring
      rw [e] at hd
      have hm1r : (-2 * σ - 2 : ℝ) ≤ m := by exact_mod_cast hm1
      have hm2r : (m : ℝ) ≤ (mxLo t Fl : ℝ) - mnLo Fl + 1 + 2 * σ + 3 := by exact_mod_cast hm2
      have hzc' := hcl z hzc
      apply hn (mxLo t Fl + 1 - z - m)
      · push_cast; linarith
      · push_cast; linarith
      · exact hd
  ·
    have hw : (wS true Fl Fc : ℤ) = 1 - mnLo Fl := by
      simp only [wS, if_true]; rw [Int.toNat_of_nonneg]; omega
    have hmA := le_mxAll' t Fl Fc
    have hh : (hS true t Fl Fc : ℤ) = mxAll t Fl Fc + (1 - mnLo Fl) + 1 := by
      simp only [hS, if_true]; rw [hw, Int.toNat_of_nonneg]; omega
    have hcl : ∀ z ∈ Fc, ((t : ℝ) - 1) / 2 + W0 ≤ z ∧
        (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + (W0 + S + η + 1) := by
      intro z hz
      have := hFc z hz
      simp only [if_true] at this
      constructor <;> linarith [this.1, this.2]
    refine ⟨?_, by omega, by omega, fun _ => by omega, by simp, hT1, hT2', ?_⟩
    · intro u hu
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hu
      have hz' := Finset.mem_val.mp hz
      have h2 := le_mxAll_of_mem t Fl Fc hz'
      have h1 : mnLo Fl ≤ z := by
        rcases Finset.mem_union.mp hz' with h | h
        · exact mnLo_le' Fl h
        · have := (hcl z h).1
          have : (0 : ℝ) < z := by linarith
          have : 0 < z := by exact_mod_cast this
          omega
      omega
    · intro x hx m hm1 hm2
      rcases Multiset.mem_filter.mp hx with ⟨hxU, hxW⟩
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hxU
      have hz' := Finset.mem_val.mp hz
      simp only [Formalism.WachCohomologyFacts.V2.InWinN, if_true] at hxW
      have hzc : z ∈ Fc := by
        rcases Finset.mem_union.mp hz' with h | h
        · exfalso; apply hxW
          have := mnLo_le' Fl h; have := le_mxLo_of_mem t Fl h
          constructor <;> omega
        · exact h
      simp only [if_true]
      intro heq
      have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub m _ l).mp heq.symm
      rw [hηS] at hm2
      rw [hw] at hd
      have hm1r : (-2 * σ - 2 : ℝ) ≤ m := by exact_mod_cast hm1
      have hm2r : (m : ℝ) ≤ (mxLo t Fl : ℝ) - mnLo Fl + 1 + 2 * σ + 3 := by exact_mod_cast hm2
      have hzc' := hcl z hzc
      apply hn (z + (1 - mnLo Fl) - m)
      · push_cast; linarith
      · push_cast; linarith
      · exact hd

end GlobalTheory.PositionData
