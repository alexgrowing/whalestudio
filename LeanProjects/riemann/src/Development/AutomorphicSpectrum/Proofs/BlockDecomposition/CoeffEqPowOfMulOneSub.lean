import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
open PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

open PowerSeries Filter Topology

theorem tendsto_coeff_mul_one_sub (G : ℂ⟦X⟧) (b : ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * (1 - C b * X))) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have e : ∀ j : ℕ, coeff (j + 1) (G * (1 - C b * X)) = coeff (j + 1) G - b * coeff j G := by
    intro j
    have : G * (1 - C b * X) = G - C b * (G * X) := by ring
    rw [this, map_sub, coeff_C_mul, coeff_succ_mul_X]
  simp only [e]
  have h1 := (tendsto_add_atTop_iff_nat 1).2 h
  simpa using h1.sub (h.const_mul b)

theorem tendsto_coeff_mul_prod (G : ℂ⟦X⟧) {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * ∏ k ∈ s, (1 - C (β k) * X))) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have : G * ((1 - C (β a) * X) * ∏ k ∈ s, (1 - C (β k) * X)) =
        (G * ∏ k ∈ s, (1 - C (β k) * X)) * (1 - C (β a) * X) := by ring
    rw [this]
    exact tendsto_coeff_mul_one_sub _ _ ih

theorem coeff_eq_pow_of_mul_one_sub (H : ℂ⟦X⟧) (b : ℂ) (h : H * (1 - C b * X) = 1) (j : ℕ) :
    coeff j H = b ^ j := by
  have e : H = 1 + C b * (H * X) := by
    calc H = H * (1 - C b * X) + C b * (H * X) := by ring
      _ = 1 + C b * (H * X) := by rw [h]
  induction j with
  | zero =>
    rw [e]; simp
  | succ j ih =>
    rw [e, map_add, coeff_C_mul, coeff_succ_mul_X, ih, pow_succ]
    simp [coeff_one, mul_comm]

theorem coeff_prod_one_sub {n : ℕ} (β : Fin n → ℂ) (r : ℕ) :
    coeff r (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) =
      (-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i := by
  classical
  have e : ∀ t : Finset (Fin n), ∏ i ∈ t, (-(C (β i) * X) : ℂ⟦X⟧) =
      C ((-1) ^ t.card * ∏ i ∈ t, β i) * X ^ t.card := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
  have e2 : (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) = ∏ i, (1 + -(C (β i) * X)) := by
    simp only [sub_eq_add_neg]
  rw [e2, Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [e, coeff_C_mul, coeff_X_pow]
  by_cases h : r = t.card
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp

theorem mk_mul_prod_eq_one {n : ℕ} (β : Fin n → ℂ) (g : ℕ → ℂ) (h0 : g 0 = 1)
    (hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1),
      ((-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i) * g (j - r) = 0) :
    (PowerSeries.mk g : ℂ⟦X⟧) * ∏ i, (1 - C (β i) * X) = 1 := by
  ext j
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_sub, coeff_mk]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [h0, coeff_one]
  · rw [hrec j hj, coeff_one, if_neg (by omega)]

end GlobalTheory.CompanionTheory.SatakeBound

theorem GlobalTheory.CompanionTheory.SatakeBound.norm_lt_one : liftZP_newton := by
  intro n β g h0 hrec hg i
  classical
  have hG := GlobalTheory.CompanionTheory.SatakeBound.mk_mul_prod_eq_one β g h0 hrec
  have hc : Filter.Tendsto (fun j => PowerSeries.coeff j (PowerSeries.mk g : PowerSeries ℂ))
      Filter.atTop (nhds 0) := by
    simpa [PowerSeries.coeff_mk] using hg
  have hH := GlobalTheory.CompanionTheory.SatakeBound.tendsto_coeff_mul_prod _ (Finset.univ.erase i) β hc
  have hone : ((PowerSeries.mk g : PowerSeries ℂ) *
      ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) *
      (1 - PowerSeries.C (β i) * PowerSeries.X) = 1 := by
    have hs := Finset.mul_prod_erase Finset.univ
      (fun k => (1 - PowerSeries.C (β k) * PowerSeries.X : PowerSeries ℂ)) (Finset.mem_univ i)
    calc _ = (PowerSeries.mk g : PowerSeries ℂ) * ((1 - PowerSeries.C (β i) * PowerSeries.X) *
          ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) := by ring
      _ = 1 := by rw [hs, hG]
  have hp := GlobalTheory.CompanionTheory.SatakeBound.coeff_eq_pow_of_mul_one_sub _ _ hone
  simp only [hp] at hH
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 hH
