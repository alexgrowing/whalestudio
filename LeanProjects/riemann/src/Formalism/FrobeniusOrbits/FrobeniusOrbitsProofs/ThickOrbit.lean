import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists

open Classical

namespace Formalism.FrobeniusOrbits
namespace ThickOrbit

theorem bound_aux {n L : ℕ} (j : ℤ) (s : ℕ) (hj : j ≤ L) (hs : 4 * L * s < n) :
    4 * (j * (s : ℤ)) < n := by
  have hs' : (4 * L * s : ℤ) < n := by exact_mod_cast hs
  have h0 : (0 : ℤ) ≤ s := by positivity
  nlinarith

theorem int_mul_lt_of_le_four_mul {n L : ℕ} (j : ℤ) (s : ℕ) (hj : j ≤ 4 * L) (hs : 4 * L * s < n) :
    j * (s : ℤ) < n := by
  have hs' : (4 * L * s : ℤ) < n := by exact_mod_cast hs
  have h0 : (0 : ℤ) ≤ s := by positivity
  nlinarith

theorem key {n L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n) (hR : NoRel T L)
    (u₀ t h : ZMod n) (hord : 4 * L < addOrderOf h) (i₀ a b c : ℤ)
    (ha : a ∈ Finset.Ico i₀ (i₀ + L)) (hc : c ∈ Finset.Ico i₀ (i₀ + L)) (hab : a < b)
    (hbc : b < c) (hxa : InTranslate T u₀ (t + a • h)) (hxb : InTranslate T u₀ (t + b • h))
    (hxc : InTranslate T u₀ (t + c • h)) : False := by
  rw [Finset.mem_Ico] at ha hc
  obtain ⟨sa, hsa, ea⟩ := hxa
  obtain ⟨sb, hsb, eb⟩ := hxb
  obtain ⟨sc, hsc, ec⟩ := hxc
  rw [zsmul_eq_mul] at ea eb ec

  have hz : ∀ d : ℤ, 0 < d → d ≤ 4 * L → (d : ZMod n) * h ≠ 0 := by
    intro d hd hdL hdz
    have hdv : (addOrderOf h : ℤ) ∣ d :=
      addOrderOf_dvd_iff_zsmul_eq_zero.mpr (by rw [zsmul_eq_mul]; exact hdz)
    have := Int.le_of_dvd hd hdv
    omega
  have hab' : sa ≠ sb := by
    rintro rfl
    exact hz (b - a) (by omega) (by omega) (by push_cast; linear_combination eb - ea)
  have hac' : sa ≠ sc := by
    rintro rfl
    exact hz (c - a) (by omega) (by omega) (by push_cast; linear_combination ec - ea)
  have hbc' : sb ≠ sc := by
    rintro rfl
    exact hz (c - b) (by omega) (by omega) (by push_cast; linear_combination ec - eb)
  set X : ℤ := (c - a) * ((sb : ℤ) - sa) - (b - a) * ((sc : ℤ) - sa) with hX
  have hX0 : (X : ZMod n) = 0 := by
    rw [hX]; push_cast
    linear_combination (↑b - ↑a) * (ec - ea) - (↑c - ↑a) * (eb - ea)
  have hdvd : (n : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X n).mp hX0
  have h1 := bound_aux (c - a) sb (by omega) (hT sb hsb)
  have h2 := bound_aux (c - a) sa (by omega) (hT sa hsa)
  have h3 := bound_aux (b - a) sc (by omega) (hT sc hsc)
  have h4 := bound_aux (b - a) sa (by omega) (hT sa hsa)
  have p1 : 0 ≤ (c - a) * (sb : ℤ) := mul_nonneg (by omega) (by positivity)
  have p2 : 0 ≤ (c - a) * (sa : ℤ) := mul_nonneg (by omega) (by positivity)
  have p3 : 0 ≤ (b - a) * (sc : ℤ) := mul_nonneg (by omega) (by positivity)
  have p4 : 0 ≤ (b - a) * (sa : ℤ) := mul_nonneg (by omega) (by positivity)
  have habs : |X| < n := by
    rw [abs_lt, hX]
    constructor <;> nlinarith
  have hXz : X = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  refine hR sa hsa sb hsb sc hsc hab' hac' hbc' (b - a) (c - a) ?_ ?_ ?_ ?_ (by omega) ?_
  · rw [abs_pos]; omega
  · rw [abs_le]; constructor <;> omega
  · rw [abs_pos]; omega
  · rw [abs_le]; constructor <;> omega
  · rw [hX] at hXz; linarith

theorem part_one {n L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n) (hR : NoRel T L)
    (u₀ t h : ZMod n) (hord : 4 * L < addOrderOf h) (i₀ : ℤ) :
    ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h))).card ≤ 2 := by
  set S := (Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h)) with hS
  by_contra hlt
  push_neg at hlt
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set a := S.min' hne
  set c := S.max' hne
  have hcard : 0 < ((S.erase c).erase a).card := by
    have h1 := Finset.pred_card_le_card_erase (s := S) (a := c)
    have h2 := Finset.pred_card_le_card_erase (s := S.erase c) (a := a)
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hcard
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hbS' : b ∈ S.erase c := Finset.mem_of_mem_erase hb
  have hbc : b ≠ c := Finset.ne_of_mem_erase hbS'
  have hbS : b ∈ S := Finset.mem_of_mem_erase hbS'
  have haS : a ∈ S := S.min'_mem hne
  have hcS : c ∈ S := S.max'_mem hne
  have hab : a < b := lt_of_le_of_ne (S.min'_le b hbS) (Ne.symm hba)
  have hbc' : b < c := lt_of_le_of_ne (S.le_max' b hbS) hbc
  rw [hS, Finset.mem_filter] at haS hbS hcS
  exact key T hT hR u₀ t h hord i₀ a b c haS.1 hcS.1 hab hbc' haS.2 hbS.2 hcS.2

theorem part_two {n L : ℕ} (hn : 0 < n) (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n)
    (u₀ t h : ZMod n) (hord : addOrderOf h ≤ 4 * L) :
    {x : ZMod n | (∃ i : ℤ, x = t + i • h) ∧ InTranslate T u₀ x}.ncard ≤ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [Set.ncard_le_one]
  rintro x ⟨⟨i, rfl⟩, s₁, hs₁, e₁⟩ y ⟨⟨i', rfl⟩, s₂, hs₂, e₂⟩
  set m := addOrderOf h with hm
  have hmpos : 0 < m := addOrderOf_pos h
  have hmh : (m : ZMod n) * h = 0 := by
    have := addOrderOf_nsmul_eq_zero h
    rwa [nsmul_eq_mul] at this
  rw [zsmul_eq_mul] at e₁ e₂
  set X : ℤ := (m : ℤ) * ((s₁ : ℤ) - s₂) with hX
  have hX0 : (X : ZMod n) = 0 := by
    rw [hX]; push_cast
    linear_combination (↑m : ZMod n) * (e₂ - e₁) + ((↑i : ZMod n) - ↑i') * hmh
  have hdvd : (n : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X n).mp hX0
  have h1 := int_mul_lt_of_le_four_mul (m : ℤ) s₁ (by exact_mod_cast hord) (hT s₁ hs₁)
  have h2 := int_mul_lt_of_le_four_mul (m : ℤ) s₂ (by exact_mod_cast hord) (hT s₂ hs₂)
  have p1 : 0 ≤ (m : ℤ) * (s₁ : ℤ) := by positivity
  have p2 : 0 ≤ (m : ℤ) * (s₂ : ℤ) := by positivity
  have habs : |X| < n := by
    rw [abs_lt, hX]
    constructor <;> nlinarith
  have hXz : X = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have hs : (s₁ : ℤ) = s₂ := by
    rw [hX] at hXz
    rcases mul_eq_zero.mp hXz with h0 | h0
    · omega
    · linarith
  have hs' : s₁ = s₂ := by exact_mod_cast hs
  subst hs'
  rw [zsmul_eq_mul, zsmul_eq_mul, e₁, e₂]

end ThickOrbit

theorem hostThickOrbit : HostThickOrbit := by
  intro n L hn _ T hT hR u₀ t h
  exact ⟨fun hord i₀ => ThickOrbit.part_one T hT hR u₀ t h hord i₀,
    fun hord => ThickOrbit.part_two hn T hT u₀ t h hord⟩

end Formalism.FrobeniusOrbits
