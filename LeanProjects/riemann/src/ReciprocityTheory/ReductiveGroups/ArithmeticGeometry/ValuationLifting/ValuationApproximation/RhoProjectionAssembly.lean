import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.LiftSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.ValuationApproximation.LargeSmall

namespace ReciprocityTheory.ChartRestriction.G.Lift.VA

open WithZero

theorem disc (M ε : WithZero (Multiplicative ℤ)) (hε : ε ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ m', m ≤ m' → ∀ g h : WithZero (Multiplicative ℤ),
      g < 1 → h ≤ M → g ^ m' * h < ε := by
  obtain ⟨e, rfl⟩ : ∃ e : ℤ, ε = exp e := ⟨log ε, (exp_log hε).symm⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ, M ≤ exp a := by
    rcases eq_or_ne M 0 with rfl | hM
    · exact ⟨0, zero_le⟩
    · exact ⟨log M, (exp_log hM).ge⟩
  refine ⟨(a - e + 1).toNat + 1, by omega, fun m' hm' g h hg hh => ?_⟩
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [zero_pow (by omega), zero_mul]
    exact exp_pos
  · have hg1 : g ≤ exp (-1) := by
      rw [← exp_log hg0] at hg ⊢
      rw [← exp_zero, exp_lt_exp] at hg
      rw [exp_le_exp]
      omega
    calc g ^ m' * h ≤ exp (-1) ^ m' * exp a :=
          mul_le_mul' (pow_le_pow_left' hg1 m') (hh.trans ha)
      _ = exp (-(m' : ℤ) + a) := by
          rw [← exp_nsmul, ← exp_add]
          congr 1
          rw [smul_neg, nsmul_eq_mul, mul_one]
      _ < exp e := by
          rw [exp_lt_exp]
          omega

section
variable {Ω : Type} [Field Ω]

theorem val_frac_of_one_lt (v : Valuation Ω (WithZero (Multiplicative ℤ))) (y : Ω) (hy : 1 < v y)
    (m : ℕ) (hm : 1 ≤ m) : v (y ^ m / (1 + y ^ m)) = 1 := by
  have h1 : 1 < v (y ^ m) := by
    rw [map_pow]
    exact one_lt_pow' hy (by omega)
  have h2 : v (1 + y ^ m) = v (y ^ m) :=
    Valuation.map_add_eq_of_lt_right v (by rw [map_one]; exact h1)
  have h3 : v (y ^ m) ≠ 0 := ne_of_gt (lt_trans zero_lt_one h1)
  rw [map_div₀, h2, div_self h3]

theorem val_frac_of_lt_one (v : Valuation Ω (WithZero (Multiplicative ℤ))) (y : Ω) (hy : v y < 1)
    (m : ℕ) (hm : 1 ≤ m) : v (y ^ m / (1 + y ^ m)) = v y ^ m := by
  have h1 : v (y ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one' hy (by omega)
  have h2 : v (1 + y ^ m) = v 1 :=
    Valuation.map_add_eq_of_lt_left v (by rw [map_one]; exact h1)
  rw [map_div₀, h2, map_one, div_one, map_pow]

theorem upgrade (v w : Valuation Ω (WithZero (Multiplicative ℤ))) (π : Ω) (hπ : v π = exp (1 : ℤ))
    (u : Ω) (hu : 1 ≤ v u) (hu' : w u < 1) : ∃ x, 1 < v x ∧ w x < 1 := by
  obtain ⟨m, -, hm⟩ := disc (w π) 1 one_ne_zero
  refine ⟨u ^ m * π, ?_, ?_⟩
  · rw [map_mul, map_pow, hπ]
    exact lt_of_lt_of_le (by rw [← exp_zero, exp_lt_exp]; norm_num)
      (le_mul_of_one_le_left' (one_le_pow_of_one_le' hu m))
  · rw [map_mul, map_pow]
    exact hm m le_rfl _ _ hu' le_rfl

end

theorem pair_separation : PairSep := by
  intro Ω _ ι _ v h1 h2 i j hij
  choose π hπ using h1
  have hex : ∃ x, ¬ (v i x ≤ 1 ↔ v j x ≤ 1) := by
    by_contra hc
    push Not at hc
    exact h2 i j hij (Valuation.isEquiv_of_val_le_one hc)
  obtain ⟨x, hx⟩ := hex
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hi0 : 0 < v i x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
  have hj0 : 0 < v j x := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
  by_cases hix : v i x ≤ 1
  · have hjx : 1 < v j x := lt_of_not_ge (fun h => hx (iff_of_true hix h))
    refine upgrade (v i) (v j) (π i) (hπ i) x⁻¹ ?_ ?_
    · rw [map_inv₀]
      exact (one_le_inv₀ hi0).mpr hix
    · rw [map_inv₀]
      exact (inv_lt_one₀ hj0).mpr hjx
  · have hix' : 1 < v i x := lt_of_not_ge hix
    have hjx : v j x ≤ 1 := by
      by_contra h
      exact hx (iff_of_false hix h)
    obtain ⟨y, hy1, hy2⟩ := upgrade (v j) (v i) (π j) (hπ j) x⁻¹
      (by rw [map_inv₀]; exact (one_le_inv₀ hj0).mpr hjx)
      (by rw [map_inv₀]; exact (inv_lt_one₀ hi0).mpr hix')
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy1
      exact absurd hy1 (not_lt.mpr zero_le)
    have hiy : 0 < v i y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
    have hjy : 0 < v j y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy0)
    refine ⟨y⁻¹, ?_, ?_⟩
    · rw [map_inv₀]
      exact (one_lt_inv₀ hiy).mpr hy2
    · rw [map_inv₀]
      exact (inv_lt_one₀ hjy).mpr hy1

theorem large_small_separation : LargeSmall := by
  intro Ω _ ι _ v hbig hpair i
  classical
  have key : ∀ S : Finset ι, i ∉ S → ∃ y, 1 < v i y ∧ ∀ j ∈ S, v j y < 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨x, hx⟩ := hbig i
      exact ⟨x, hx, by simp⟩
    | insert k S hk IH =>
      intro hiS
      have hki : k ≠ i := fun h => hiS (h ▸ Finset.mem_insert_self k S)
      have hiS' : i ∉ S := fun h => hiS (Finset.mem_insert_of_mem h)
      obtain ⟨y, hy1, hyS⟩ := IH hiS'
      obtain ⟨w, hw1, hw2⟩ := hpair i k (Ne.symm hki)
      obtain ⟨m, hm1, hm⟩ := disc (Finset.univ.sup fun j => v j w) 1 one_ne_zero
      have hwM : ∀ j, v j w ≤ Finset.univ.sup fun j => v j w :=
        fun j => Finset.le_sup (f := fun j => v j w) (Finset.mem_univ j)
      by_cases hky : v k y ≤ 1
      · refine ⟨y ^ m * w, ?_, ?_⟩
        · rw [map_mul, map_pow]
          exact lt_of_lt_of_le hw1 (le_mul_of_one_le_left' (one_le_pow_of_one_le' hy1.le m))
        · intro j hj
          rw [map_mul, map_pow]
          rcases Finset.mem_insert.mp hj with rfl | hjS
          · exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' hky m)) hw2
          · exact hm m le_rfl _ _ (hyS j hjS) (hwM j)
      · have hky' : 1 < v k y := lt_of_not_ge hky
        refine ⟨y ^ m / (1 + y ^ m) * w, ?_, ?_⟩
        · rw [map_mul, val_frac_of_one_lt (v i) y hy1 m hm1, one_mul]
          exact hw1
        · intro j hj
          rw [map_mul]
          rcases Finset.mem_insert.mp hj with rfl | hjS
          · rw [val_frac_of_one_lt (v j) y hky' m hm1, one_mul]
            exact hw2
          · rw [val_frac_of_lt_one (v j) y (hyS j hjS) m hm1]
            exact hm m le_rfl _ _ (hyS j hjS) (hwM j)
  obtain ⟨y, hy1, hy2⟩ := key (Finset.univ.erase i) (Finset.notMem_erase i _)
  exact ⟨y, hy1, fun j hj => hy2 j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)⟩

theorem near_one_approximation : NearOne := by
  intro Ω _ ι _ v hls i ε hε
  classical
  choose mj hmj1 hmj using fun j => disc 1 (ε j) (hε j)
  obtain ⟨y, hy1, hy2⟩ := hls i
  set m := (Finset.univ.sup mj) + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmj' : ∀ j, mj j ≤ m := fun j =>
    le_trans (Finset.le_sup (f := mj) (Finset.mem_univ j)) (Nat.le_succ _)
  refine ⟨y ^ m / (1 + y ^ m), val_frac_of_one_lt (v i) y hy1 m hm1, fun j hj => ?_⟩
  rw [val_frac_of_lt_one (v j) y (hy2 j hj) m hm1, ← mul_one (v j y ^ m)]
  exact hmj j m (hmj' j) _ _ (hy2 j hj) le_rfl

theorem rho_projection_assembly : Assembly := by
  intro Ω _ ι _ v h1 hN n
  classical
  choose π hπ using h1
  have hπ0 : ∀ i, π i ≠ 0 := by
    intro i h
    have := hπ i
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  set t : ι → Ω := fun i => π i ^ n i with ht
  have ht0 : ∀ i k, 0 < v k (t i) := fun i k =>
    zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (zpow_ne_zero _ (hπ0 i)))
  have hε : ∀ i k, exp (n k) * (v k (t i))⁻¹ ≠ 0 := fun i k =>
    mul_ne_zero exp_ne_zero (inv_ne_zero (ht0 i k).ne')
  choose z hz1 hz2 using fun i => hN i (fun k => exp (n k) * (v k (t i))⁻¹) (hε i)
  refine ⟨∑ i, z i * t i, fun k => ?_⟩
  have hmain : v k (z k * t k) = exp (n k) := by
    rw [map_mul, hz1 k, one_mul, ht]
    simp only
    rw [map_zpow₀, hπ k, ← exp_zsmul, smul_eq_mul, mul_one]
  have hrest : v k (∑ i ∈ Finset.univ.erase k, z i * t i) < exp (n k) := by
    refine Valuation.map_sum_lt _ exp_ne_zero (fun i hi => ?_)
    have hik : k ≠ i := fun h => (Finset.mem_erase.mp hi).1 h.symm
    rw [map_mul]
    exact (lt_mul_inv_iff₀ (ht0 i k)).mp (hz2 i k hik)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Valuation.map_add_eq_of_lt_left _ (hmain ▸ hrest), hmain]

end ReciprocityTheory.ChartRestriction.G.Lift.VA
