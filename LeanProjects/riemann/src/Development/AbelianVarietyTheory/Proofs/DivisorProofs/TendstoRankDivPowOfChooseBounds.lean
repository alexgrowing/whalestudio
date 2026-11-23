import Mathlib

open Filter Topology

namespace GlobalTheory

theorem tendsto_div_add_const_pow_div_pow (e K : ℝ) (he : e ≠ 0) (D : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
  have h1 : Tendsto (fun m : ℕ => (1 / e + K / (m : ℝ)) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat K).const_add (1 / e)).pow D
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← div_pow]
  congr 1
  field_simp

theorem tendsto_rank_div_pow_of_choose_bounds (D e δ : ℕ) (r : ℕ → ℕ) (he : 0 < e)
    (h : ∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ,
      δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) :
    Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
      (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  choose! c c' hc using h
  set C := ∑ s ∈ Finset.range e, c s with hC
  set C' := ∑ s ∈ Finset.range e, c' s with hC'
  have hcC : ∀ s, s < e → c s ≤ C := fun s hs =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have hcC' : ∀ s, s < e → c' s ≤ C' := fun s hs =>
    Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hlim : ∀ K : ℝ, Tendsto (fun m : ℕ => (δ : ℝ) / D.factorial *
      (((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D)) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
    intro K
    have := (tendsto_div_add_const_pow_div_pow e K heR.ne' D).const_mul ((δ : ℝ) / D.factorial)
    convert this using 2
    rw [div_pow, one_pow]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-(C : ℝ))) (hlim ((C' + D : ℕ) : ℝ)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (e * C + 1)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have hqC : C ≤ m / e := (Nat.le_div_iff_mul_le he).2 (by nlinarith)
    have hcs := hcC (m % e) hs
    have h1 := (hc (m % e) hs (m / e - c (m % e))).1
    rw [Nat.sub_add_cancel (by omega : c (m % e) ≤ m / e), hm_eq] at h1
    have h2 := Nat.pow_le_choose (α := ℝ) D (m / e - c (m % e) + D)
    have h3 : m / e - c (m % e) + D + 1 - D = m / e - c (m % e) + 1 := by omega
    rw [h3] at h2
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hsR : ((m % e : ℕ) : ℝ) < e := by exact_mod_cast hs
    have hlt : (m : ℝ) / e < ((m / e : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ heR]; nlinarith
    have hge : (C : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]
      have : ((e * C : ℕ) : ℝ) ≤ m := by exact_mod_cast (show e * C ≤ m by omega)
      push_cast at this; linarith
    have hcsR : (c (m % e) : ℝ) ≤ C := by exact_mod_cast hcs
    have hx : (m : ℝ) / e + -(C : ℝ) ≤ ((m / e - c (m % e) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]; linarith
    have hx0 : 0 ≤ (m : ℝ) / e + -(C : ℝ) := by linarith
    have hA : (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D ≤ r m := by
      calc (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D
          ≤ (δ : ℝ) / D.factorial * (((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D := by gcongr
        _ = (δ : ℝ) * ((((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D / D.factorial) := by ring
        _ ≤ (δ : ℝ) * ((m / e - c (m % e) + D).choose D : ℝ) := by gcongr
        _ ≤ r m := by exact_mod_cast h1
    calc (δ : ℝ) / D.factorial * (((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D)
        = (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D := by ring
      _ ≤ (r m : ℝ) / (m : ℝ) ^ D := by gcongr
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have h1 := (hc (m % e) hs (m / e)).2
    rw [hm_eq] at h1
    have h2 := Nat.choose_le_pow_div (α := ℝ) D (m / e + c' (m % e) + D)
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hs0 : (0 : ℝ) ≤ ((m % e : ℕ) : ℝ) := Nat.cast_nonneg _
    have hle : ((m / e : ℕ) : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]; nlinarith
    have hcsR : (c' (m % e) : ℝ) ≤ C' := by exact_mod_cast hcC' (m % e) hs
    have hx : ((m / e + c' (m % e) + D : ℕ) : ℝ) ≤ (m : ℝ) / e + ((C' + D : ℕ) : ℝ) := by
      push_cast; linarith
    have hA : (r m : ℝ) ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D := by
      calc (r m : ℝ) ≤ (δ : ℝ) * ((m / e + c' (m % e) + D).choose D : ℝ) := by exact_mod_cast h1
        _ ≤ (δ : ℝ) * (((m / e + c' (m % e) + D : ℕ) : ℝ) ^ D / D.factorial) := by gcongr
        _ = (δ : ℝ) / D.factorial * (((m / e + c' (m % e) + D : ℕ) : ℝ)) ^ D := by ring
        _ ≤ _ := by gcongr
    calc (r m : ℝ) / (m : ℝ) ^ D
        ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D / (m : ℝ) ^ D := by gcongr
      _ = _ := by ring

end GlobalTheory
