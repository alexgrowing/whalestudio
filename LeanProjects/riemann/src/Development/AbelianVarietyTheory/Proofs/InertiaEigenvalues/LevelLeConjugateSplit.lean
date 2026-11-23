import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair

namespace GlobalTheory.LamTie.ConjLevel

variable {E : Type} [Field E] [NumberField E]

theorem exists_cong_one [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  obtain ⟨b, hb⟩ := exists_int_cong P z hz
  obtain ⟨a, ha⟩ := (hef P hP).2.2 b
  have h3 := OrderUnits.val_int_le P 1 _ (by simpa using ha)
  refine ⟨a, ?_⟩
  rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
  have := Valuation.map_sub_le _ hb h3
  rw [sub_sub_sub_cancel_left] at this
  exact this

theorem exists_cong [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (m : ℕ) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-(m : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  induction m with
  | zero => exact ⟨0, by simpa [iota_zero, zero_coord] using hz⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨t, ht, ht'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top m
    have hv : Valued.v (iota t P) = WithZero.exp (-(m : ℤ)) := by
      refine eq_exp_of_le (val_iota_le_of_mem hP m ht) fun h3 => ht' ?_
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      convert h3 using 2
      push_cast; ring
    have ht0 : iota t P ≠ 0 := fun h => by
      rw [h, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨c, hc⟩ := exists_cong_one hs hP ((iota a P - z) / iota t P) (by
      rw [map_div₀, hv, div_le_one₀ WithZero.exp_pos]; exact ha)
    refine ⟨a - t * c, ?_⟩
    have : iota (a - t * c) P - z = -(iota t P * (iota c P - (iota a P - z) / iota t P)) := by
      rw [iota_sub, iota_mul, sub_coord, mul_coord]; field_simp; ring
    rw [this, Valuation.map_neg, map_mul, hv]
    refine (mul_le_mul' le_rfl hc).trans_eq ?_
    rw [← WithZero.exp_add]
    congr 1
    push_cast; ring

theorem levelLe_of_split [IsCMField E] {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} (hs : Splits v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hP' : Over P' v) {n : ℕ} (hn : LevelLe χ P n) : LevelLe χ P' n := by
  by_cases hne : P = P'
  · exact hne ▸ hn
  obtain ⟨h2, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  have hmul := loc_mul_loc hF hP hP' hne (h2 P P' hP hP' hne)
  obtain ⟨m, hm⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P'
  intro u hu hu'
  have hu1 : Valued.v (u : P'.adicCompletion E) = 1 := hu
  obtain ⟨a, h4⟩ := exists_cong hs hP' (m + n + 1) u hu1.le
  have hlt : WithZero.exp (-((m + n + 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hlt1 : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (iota a P') = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ h4.trans_lt hlt), hu1]
  have hav : a ∉ v.asIdeal ^ 1 := fun h => (h5 ▸ val_iota_le_of_mem hP' 1 h).not_gt hlt1
  have ha0 : a ≠ 0 := fun h => hav (h ▸ zero_mem _)
  have hunit : Valued.v (iota a P) = 1 := by
    have := eq_exp_of_le (m := 0) (by simpa using val_iota_le_one P a) fun h3 => hav (by
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      simpa using h3)
    simpa using this
  have hsub : a - 1 ∈ v.asIdeal ^ n := by
    rw [← (hef P' hP').2.1, ← val_iota_le_iff, iota_sub, iota_one, sub_coord, one_coord]
    have := Valuation.map_add_le _ (h4.trans (WithZero.exp_le_exp.2
      (show -((m + n + 1 : ℕ) : ℤ) ≤ -(n : ℤ) by omega))) hu'
    rwa [sub_add_sub_cancel] at this
  have h6 : χ.loc P (locF P a ha0) = 1 := by
    refine hn _ hunit ?_
    have := val_iota_le_of_mem hP n hsub
    rw [iota_sub, iota_one, sub_coord, one_coord] at this
    exact this
  have h7 := hmul a ha0
  rw [h6, one_mul] at h7
  have h8 : χ.loc P' (locF P' a ha0 / u) = 1 := by
    refine hm _ ?_ ?_
    · show Valued.v ((locF P' a ha0 / u : (P'.adicCompletion E)ˣ) : P'.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, coe_locF, h5, hu1, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, coe_locF]
      exact h4.trans (WithZero.exp_le_exp.2 (by omega))
  rw [map_div, div_eq_one, h7] at h8
  exact h8.symm

open Formalism.BasicNotions GlobalTheory.ToricDenom in

theorem levelLe_conj : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : Formalism.L2.Host.HChar H.E), χ.TrivOn H.F →
    ∀ w w' : HeightOneSpectrum (𝓞 H.E), below w = below w' → Splits (below w) → ∀ n : ℕ, χ.LevelLe w n → χ.LevelLe w' n := by
  intro R H χ hF w w' hw hs n hn
  have : IsCMField H.E := H.isCMField_hostE
  exact levelLe_of_split hF hs (over_below w) (hw ▸ over_below w') hn

end GlobalTheory.LamTie.ConjLevel
