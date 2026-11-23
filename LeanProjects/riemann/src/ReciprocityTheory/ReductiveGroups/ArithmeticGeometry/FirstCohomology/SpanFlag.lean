import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.IndepOfFlag

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1.RB

open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma greedy [FiniteDimensional ℝ E] (X : Submodule ℤ E) [DiscreteTopology X] {d : ℕ}
    (v : Fin d → E) (hv : LinearIndependent ℝ v) (hvX : ∀ i, v i ∈ X) :
    ∃ u : Fin d → E, ∀ k : Fin d, u k ∈ X ∧ u k ∉ V u k.val ∧ (∃ i, ‖u k‖ ≤ ‖v i‖) ∧
      ∀ z ∈ X, z ∉ V u k.val → ‖u k‖ ≤ ‖z‖ := by
  classical
  have hstep : ∀ (u : Fin d → E) (n : ℕ), n < d → ∃ w ∈ X, w ∉ V u n ∧ (∃ i, ‖w‖ ≤ ‖v i‖) ∧
      ∀ z ∈ X, z ∉ V u n → ‖w‖ ≤ ‖z‖ := by
    intro u n hn
    have hex : ∃ i, v i ∉ V u n := by
      by_contra h
      push_neg at h
      have hle : span ℝ (Set.range v) ≤ V u n :=
        span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
      have h1 : finrank ℝ (span ℝ (Set.range v)) = d := by
        rw [finrank_span_eq_card hv, Fintype.card_fin]
      have h2 : finrank ℝ (V u n) ≤ n := by
        have hV : V u n = span ℝ (Set.range (fun i : Fin n => u (Fin.castLE hn.le i))) := by
          unfold V
          congr 1
          ext x
          simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
          constructor
          · rintro ⟨l, hl, rfl⟩
            exact ⟨⟨l.val, hl⟩, rfl⟩
          · rintro ⟨i, rfl⟩
            exact ⟨Fin.castLE hn.le i, i.isLt, rfl⟩
        rw [hV]
        exact (finrank_range_le_card _).trans (by simp)
      have h3 := Submodule.finrank_mono hle
      omega
    obtain ⟨i0, hi0⟩ := hex
    have hAfin : {z : E | z ∈ X ∧ z ∉ V u n ∧ ‖z‖ ≤ ‖v i0‖}.Finite :=
      (finite_ball X ‖v i0‖).subset (by
        rintro z ⟨hzX, -, hz⟩
        exact ⟨mem_closedBall_zero_iff.mpr hz, hzX⟩)
    obtain ⟨w, ⟨hwX, hwV, hwle⟩, hwmin⟩ :=
      Set.exists_min_image _ (fun z => ‖z‖) hAfin ⟨v i0, hvX i0, hi0, le_rfl⟩
    refine ⟨w, hwX, hwV, ⟨i0, hwle⟩, fun z hzX hzV => ?_⟩
    by_cases hz : ‖z‖ ≤ ‖v i0‖
    · exact hwmin z ⟨hzX, hzV, hz⟩
    · exact hwle.trans (le_of_not_ge hz)
  have hVupd : ∀ (u : Fin d → E) (i : Fin d) (w : E) (n : ℕ), n ≤ i.val →
      V (Function.update u i w) n = V u n := by
    intro u i w n hn
    unfold V
    congr 1
    apply Set.image_congr
    intro l hl
    have hli : l ≠ i := by
      intro h
      subst h
      simp only [Set.mem_setOf_eq] at hl
      omega
    simp [Function.update_of_ne hli]
  have key : ∀ n ≤ d, ∃ u : Fin d → E, ∀ k : Fin d, k.val < n → (u k ∈ X ∧ u k ∉ V u k.val ∧
      (∃ i, ‖u k‖ ≤ ‖v i‖) ∧ ∀ z ∈ X, z ∉ V u k.val → ‖u k‖ ≤ ‖z‖) := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨u, hu⟩ := ih (by omega)
      obtain ⟨w, hw⟩ := hstep u n (by omega)
      refine ⟨Function.update u ⟨n, by omega⟩ w, fun k hk => ?_⟩
      rw [hVupd u ⟨n, by omega⟩ w k.val (by show k.val ≤ n; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · have hki : k ≠ ⟨n, by omega⟩ := by
          intro h
          rw [h] at hk
          exact lt_irrefl _ hk
        rw [Function.update_of_ne hki]
        exact hu k hk
      · have hki : k = ⟨n, by omega⟩ := Fin.ext hk
        rw [hki, Function.update_self]
        exact hw
  obtain ⟨u, hu⟩ := key d le_rfl
  exact ⟨u, fun k => hu k k.isLt⟩

lemma exists_b [FiniteDimensional ℝ E] {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u)
    (X : Submodule ℤ E) [DiscreteTopology X] (hX : ∀ l, u l ∈ X) (k : Fin d)
    (hmono : ∀ j : Fin d, j < k → ‖u j‖ ≤ ‖u k‖) :
    ∃ b : E, b ∈ X ∧ b ∈ V u (k.val + 1) ∧ 0 < phi u k b ∧ phi u k b ≤ 1 ∧
      (∀ x ∈ X, x ∈ V u (k.val + 1) → 0 < phi u k x → phi u k x ≤ 1 → phi u k b ≤ phi u k x) ∧
      (∀ x ∈ X, x ∈ V u (k.val + 1) → phi u k x = phi u k b → ‖b‖ ≤ ‖x‖) ∧
      ‖b‖ ^ 2 ≤ d * ‖u k‖ ^ 2 := by
  classical
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.succ_le_of_lt k.pos
  have hR : 0 ≤ Real.sqrt d * ‖u k‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hBfin : {y : E | y ∈ X ∧ y ∈ V u (k.val + 1) ∧ 0 < phi u k y ∧ phi u k y ≤ 1 ∧
      ‖y‖ ^ 2 ≤ d * ‖u k‖ ^ 2}.Finite :=
    (finite_ball X (Real.sqrt d * ‖u k‖)).subset (by
      rintro y ⟨hyX, -, -, -, hy⟩
      refine ⟨mem_closedBall_zero_iff.mpr ?_, hyX⟩
      have h2 : ‖y‖ ^ 2 ≤ (Real.sqrt d * ‖u k‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
        exact hy
      by_contra hc
      push_neg at hc
      nlinarith [norm_nonneg y])
  have hBne : ({y : E | y ∈ X ∧ y ∈ V u (k.val + 1) ∧ 0 < phi u k y ∧ phi u k y ≤ 1 ∧
      ‖y‖ ^ 2 ≤ d * ‖u k‖ ^ 2}).Nonempty :=
    ⟨u k, hX k, mem_V_of_lt u (Nat.lt_succ_self _), by rw [phi_self u k hu]; exact one_pos,
      (phi_self u k hu).le, le_mul_of_one_le_left (sq_nonneg _) hd⟩
  obtain ⟨b0, hb0B, hb0min⟩ := Set.exists_min_image _ (phi u k) hBfin hBne
  have hCfin : {y : E | (y ∈ X ∧ y ∈ V u (k.val + 1) ∧ 0 < phi u k y ∧ phi u k y ≤ 1 ∧
      ‖y‖ ^ 2 ≤ d * ‖u k‖ ^ 2) ∧ phi u k y = phi u k b0}.Finite :=
    hBfin.subset (fun y hy => hy.1)
  obtain ⟨b, ⟨⟨hbX, hbV, hb0, hb1, hbd⟩, hbphi⟩, hbmin⟩ :=
    Set.exists_min_image _ (fun y => ‖y‖) hCfin ⟨b0, hb0B, rfl⟩
  refine ⟨b, hbX, hbV, hb0, hb1, ?_, ?_, hbd⟩
  · intro x hxX hxV h0 h1
    obtain ⟨y, hyX, hyV, hyphi, hyd⟩ :=
      reduce u hu X hX k hmono hxX hxV (abs_le.mpr ⟨by linarith, h1⟩)
    have hy0 : 0 < phi u k y := by rw [hyphi]; exact h0
    have hy1 : phi u k y ≤ 1 := by rw [hyphi]; exact h1
    rw [hbphi, ← hyphi]
    exact hb0min y ⟨hyX, hyV, hy0, hy1, hyd⟩
  · intro x hxX hxV hx
    by_cases hxd : ‖x‖ ^ 2 ≤ d * ‖u k‖ ^ 2
    · have hx0 : 0 < phi u k x := by rw [hx]; exact hb0
      have hx1 : phi u k x ≤ 1 := by rw [hx]; exact hb1
      exact hbmin x ⟨⟨hxX, hxV, hx0, hx1, hxd⟩, hx.trans hbphi⟩
    · push_neg at hxd
      have hlt : ‖b‖ ^ 2 < ‖x‖ ^ 2 := lt_of_le_of_lt hbd hxd
      by_contra hc
      push_neg at hc
      nlinarith [norm_nonneg b, norm_nonneg x]

lemma span_flag {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u) (X : Submodule ℤ E)
    (b : Fin d → E) (hbX : ∀ k, b k ∈ X) (hbV : ∀ k : Fin d, b k ∈ V u (k.val + 1))
    (hb0 : ∀ k, 0 < phi u k (b k)) (hb1 : ∀ k, phi u k (b k) ≤ 1)
    (hbmin : ∀ k : Fin d, ∀ x ∈ X, x ∈ V u (k.val + 1) → 0 < phi u k x → phi u k x ≤ 1 →
      phi u k (b k) ≤ phi u k x) :
    ∀ n ≤ d, ∀ x ∈ X, x ∈ V u n → x ∈ span ℤ (Set.range b) := by
  intro n
  induction n with
  | zero =>
    intro _ x _ hx
    obtain ⟨c, hc, rfl⟩ := exists_coeffs u hx
    have hc0 : ∀ l, c l = 0 := fun l => hc l (Nat.zero_le _)
    simp [hc0]
  | succ n ih =>
    intro hn x hxX hxV
    have hkV : x ∈ V u ((⟨n, by omega⟩ : Fin d).val + 1) := hxV
    have htpos : 0 < phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩) := hb0 _
    obtain ⟨q, hq⟩ : ∃ q : ℤ, q = ⌊phi u ⟨n, by omega⟩ x / phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩)⌋ :=
      ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : E, y = x - (q : ℝ) • b ⟨n, by omega⟩ := ⟨_, rfl⟩
    have hyX : y ∈ X := by
      rw [hy, Int.cast_smul_eq_zsmul]
      exact X.sub_mem hxX (X.smul_mem q (hbX _))
    have hyV : y ∈ V u ((⟨n, by omega⟩ : Fin d).val + 1) := by
      rw [hy]
      exact Submodule.sub_mem _ hkV (Submodule.smul_mem _ _ (hbV _))
    have hyphi : phi u ⟨n, by omega⟩ y =
        phi u ⟨n, by omega⟩ x - q * phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩) := by
      rw [hy, phi_sub, phi_smul]
    have hlo : 0 ≤ phi u ⟨n, by omega⟩ y := by
      rw [hyphi]
      have h1 := Int.floor_le (phi u ⟨n, by omega⟩ x / phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩))
      rw [← hq] at h1
      have h2 := mul_le_mul_of_nonneg_right h1 htpos.le
      rw [div_mul_cancel₀ _ htpos.ne'] at h2
      linarith
    have hhi : phi u ⟨n, by omega⟩ y < phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩) := by
      rw [hyphi]
      have h1 := Int.lt_floor_add_one
        (phi u ⟨n, by omega⟩ x / phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩))
      rw [← hq] at h1
      have h2 := mul_lt_mul_of_pos_right h1 htpos
      rw [div_mul_cancel₀ _ htpos.ne'] at h2
      linarith
    have hy0 : phi u ⟨n, by omega⟩ y = 0 := by
      by_contra hne
      have hpos : 0 < phi u ⟨n, by omega⟩ y := lt_of_le_of_ne hlo (Ne.symm hne)
      have h3 := hbmin _ y hyX hyV hpos (hhi.le.trans (hb1 _))
      linarith
    have hyVn : y ∈ V u n := by
      have h4 := decomp u ⟨n, by omega⟩ hu hyV
      rwa [hy0, zero_smul, sub_zero] at h4
    have hyspan := ih (by omega) y hyX hyVn
    have hxy : x = y + q • b ⟨n, by omega⟩ := by
      rw [hy, Int.cast_smul_eq_zsmul]
      abel
    rw [hxy]
    exact (span ℤ (Set.range b)).add_mem hyspan
      ((span ℤ (Set.range b)).smul_mem q (subset_span ⟨_, rfl⟩))

end ReciprocityTheory.ChartRestriction.G.H1.RB
