import Formalism.LatticeRigidity.StatementC

namespace Formalism.SA.P

open NumberField Finset

theorem absNorm_le_norm {E : Type} [Field E] [NumberField E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ |(Algebra.norm ℚ l : ℝ)| := by
  have hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ b := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem]; exact hl
  set c := b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l with hc
  have hbc : b * c = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l := by
    rw [hc, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  have hc1 : c ≤ 1 := by
    have h1 : c ≤ b⁻¹ * b := by
      first
        | exact mul_le_mul_right hs _
        | (rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
           exact Submodule.mul_le_mul_right (FractionalIdeal.coe_le_coe.mpr hs))
    rwa [inv_mul_cancel₀ hb] at h1
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hc1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hbc
    exact hl0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp hbc.symm)
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hc0
    rw [← hI]
    exact FractionalIdeal.coeIdeal_eq_zero.mpr rfl
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm c := by
    rw [← hI, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have key : FractionalIdeal.absNorm b * FractionalIdeal.absNorm c = |Algebra.norm ℚ l| := by
    rw [← map_mul, hbc, FractionalIdeal.absNorm_span_singleton (𝓞 E)]
  have h0 := FractionalIdeal.absNorm_nonneg b
  have hq : FractionalIdeal.absNorm b ≤ |Algebra.norm ℚ l| := by
    rw [← key]; nlinarith
  have hr : ((FractionalIdeal.absNorm b : ℚ) : ℝ) ≤ ((|Algebra.norm ℚ l| : ℚ) : ℝ) := by
    exact_mod_cast hq
  rwa [Rat.cast_abs] at hr

variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]

theorem sqrt_absNorm_le_prod (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    √(FractionalIdeal.absNorm b : ℝ) ≤ ∏ w : InfinitePlace E, w l := by
  have h1 := absNorm_le_norm b hb l hl hl0
  have h2 : |((Algebra.norm ℚ l : ℚ) : ℝ)| = (∏ w : InfinitePlace E, w l) ^ 2 := by
    rw [← Rat.cast_abs, ← NumberField.InfinitePlace.prod_eq_abs_norm, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hw : w.mult = 2 :=
      NumberField.InfinitePlace.mult_isComplex ⟨w, NumberField.IsTotallyComplex.isComplex w⟩
    rw [hw]
  have hP : 0 ≤ ∏ w : InfinitePlace E, w l :=
    Finset.prod_nonneg fun w _ => (NumberField.InfinitePlace.pos_iff.mpr hl0).le
  rw [h2] at h1
  calc √(FractionalIdeal.absNorm b : ℝ) ≤ √((∏ w : InfinitePlace E, w l) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ∏ w : InfinitePlace E, w l := Real.sqrt_sq hP

theorem absNorm_pos (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) :
    (0 : ℝ) < (FractionalIdeal.absNorm b : ℝ) := by
  have h : FractionalIdeal.absNorm b * FractionalIdeal.absNorm b⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  have h0 := FractionalIdeal.absNorm_nonneg b
  have hq : (0 : ℚ) < FractionalIdeal.absNorm b := by
    refine lt_of_le_of_ne h0 ?_
    intro h'
    rw [← h', zero_mul] at h
    exact zero_ne_one h
  exact_mod_cast hq

private theorem absNorm_le_prod_infinitePlace_sq (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ ∏ w : InfinitePlace E, w l ^ 2 := by
  have h := sqrt_absNorm_le_prod b hb l hl hl0
  have hN' : (0 : ℝ) ≤ (FractionalIdeal.absNorm b : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg b
  rw [Finset.prod_pow, ← Real.sq_sqrt hN']
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

private theorem floor_mem_Icc_neg_ceil_ceil (x s : ℝ) (h : |x| < s) : ⌊x⌋ ∈ Finset.Icc (-⌈s⌉) ⌈s⌉ := by
  rw [Finset.mem_Icc]
  have h1 := abs_lt.mp h
  have h2 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h3 : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  have h4 : s ≤ ⌈s⌉ := Int.le_ceil s
  have h5 : (⌊x⌋ : ℝ) < ⌈s⌉ := by linarith
  have h6 : ((-⌈s⌉ - 1 : ℤ) : ℝ) < ⌊x⌋ := by push_cast; linarith
  have h5' : ⌊x⌋ < ⌈s⌉ := by exact_mod_cast h5
  have h6' : -⌈s⌉ - 1 < ⌊x⌋ := by exact_mod_cast h6
  constructor <;> omega

private theorem card_Icc_neg_self_eq (m : ℤ) (hm : 0 ≤ m) :
    ((Finset.Icc (-m) m).card : ℝ) = 2 * (m : ℝ) + 1 := by
  rw [Int.card_Icc, show m + 1 - -m = 2 * m + 1 by ring]
  have h0 : (0 : ℤ) ≤ 2 * m + 1 := by omega
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  push_cast
  ring

theorem card_box_le (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (ρ : InfinitePlace E → ℝ) (hρ : ∀ w, 0 < ρ w) (P : Finset E)
    (hP : ∀ l ∈ P, l ∈ b ∧ l ≠ 0 ∧ ∀ w, w l < ρ w) :
    (P.card : ℝ) ≤ (100 : ℝ) ^ Fintype.card (InfinitePlace E) * (∏ w, ρ w ^ 2) /
      (FractionalIdeal.absNorm b : ℝ) := by
  classical
  set d := Fintype.card (InfinitePlace E) with hd
  set N : ℝ := (FractionalIdeal.absNorm b : ℝ) with hNdef
  set R : ℝ := ∏ w, ρ w ^ 2 with hRdef
  have hN : 0 < N := absNorm_pos b hb
  have hR : 0 < R := Finset.prod_pos fun w _ => by have := hρ w; positivity
  have hd1 : 0 < d := Fintype.card_pos
  by_cases hX : N ≤ 2 ^ d * R
  swap
  · rcases P.eq_empty_or_nonempty with h | ⟨l, hlP⟩
    · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
    · exfalso
      obtain ⟨hlb, hl0, hlt⟩ := hP l hlP
      apply hX
      have h1 := absNorm_le_prod_infinitePlace_sq b hb l hlb hl0
      have h2 : ∏ w : InfinitePlace E, w l ^ 2 ≤ ∏ w, ρ w ^ 2 :=
        Finset.prod_le_prod (fun w _ => by positivity)
          (fun w _ => pow_le_pow_left₀ (NumberField.InfinitePlace.pos_iff.mpr hl0).le (hlt w).le 2)
      have h3 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      nlinarith

  set X : ℝ := 2 ^ d * R / N with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef, le_div_iff₀ hN]; linarith
  set s : ℝ := X ^ ((1 : ℝ) / (2 * d)) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_rpow hX1 (by positivity)
  have hs0 : 0 < s := by linarith
  have hsX : s ^ (2 * d) = X := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have : (1 : ℝ) / (2 * d) * ((2 * d : ℕ) : ℝ) = 1 := by
      push_cast
      have : (0 : ℝ) < d := by exact_mod_cast hd1
      field_simp
    rw [this, Real.rpow_one]
  set m : ℤ := ⌈s⌉ with hmdef
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) < ⌈s⌉ := lt_of_lt_of_le hs0 (Int.le_ceil s)
    have : (0 : ℤ) < ⌈s⌉ := by exact_mod_cast this
    omega
  let f : E → InfinitePlace E → ℤ × ℤ := fun l w =>
    (⌊(w.embedding l).re / (ρ w / s)⌋, ⌊(w.embedding l).im / (ρ w / s)⌋)
  let T : Finset (InfinitePlace E → ℤ × ℤ) :=
    Fintype.piFinset fun _ => (Finset.Icc (-m) m) ×ˢ (Finset.Icc (-m) m)
  have hmaps : Set.MapsTo f ↑P ↑T := by
    intro l hlP
    obtain ⟨_, _, hlt⟩ := hP l (Finset.mem_coe.mp hlP)
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro w
    have hδ : 0 < ρ w / s := div_pos (hρ w) hs0
    have hz : ‖w.embedding l‖ < ρ w := by
      rw [NumberField.InfinitePlace.norm_embedding_eq]; exact hlt w
    have key : ∀ y : ℝ, |y| ≤ ‖w.embedding l‖ → |y / (ρ w / s)| < s := by
      intro y hy
      rw [abs_div, abs_of_pos hδ, div_lt_iff₀ hδ]
      have : s * (ρ w / s) = ρ w := by field_simp
      rw [this]; linarith
    rw [Finset.mem_product]
    exact ⟨floor_mem_Icc_neg_ceil_ceil _ _ (key _ (Complex.abs_re_le_norm _)),
      floor_mem_Icc_neg_ceil_ceil _ _ (key _ (Complex.abs_im_le_norm _))⟩
  have hinj : Set.InjOn f ↑P := by
    intro l hlP l' hlP' hfl
    obtain ⟨hlb, hl0, _⟩ := hP l (Finset.mem_coe.mp hlP)
    obtain ⟨hlb', hl0', _⟩ := hP l' (Finset.mem_coe.mp hlP')
    by_contra hne
    have hsub0 : l - l' ≠ 0 := sub_ne_zero.mpr hne
    have hsubb : l - l' ∈ b := by
      have := Submodule.sub_mem (b : Submodule (𝓞 E) E) (FractionalIdeal.mem_coe.mpr hlb)
        (FractionalIdeal.mem_coe.mpr hlb')
      exact FractionalIdeal.mem_coe.mp this
    have hlow := absNorm_le_prod_infinitePlace_sq b hb (l - l') hsubb hsub0
    have hsmall : ∀ w, w (l - l') ^ 2 < 2 * (ρ w / s) ^ 2 := by
      intro w
      have hδ : 0 < ρ w / s := div_pos (hρ w) hs0
      have hfw := congrFun hfl w
      simp only [f, Prod.mk.injEq] at hfw
      have hre := Int.abs_sub_lt_one_of_floor_eq_floor hfw.1
      have him := Int.abs_sub_lt_one_of_floor_eq_floor hfw.2
      rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at hre him
      rw [← NumberField.InfinitePlace.norm_embedding_eq, map_sub, Complex.sq_norm,
        Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      have h1 := abs_lt.mp hre
      have h2 := abs_lt.mp him
      nlinarith
    have hprod : ∏ w : InfinitePlace E, (2 * (ρ w / s) ^ 2) = N := by
      have e1 : ∏ w : InfinitePlace E, (2 * (ρ w / s) ^ 2) = 2 ^ d * R / s ^ (2 * d) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hd]
        simp only [div_pow]
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← hd, ← hRdef, ← pow_mul,
          mul_comm 2 d, mul_div_assoc]
      rw [e1, hsX, hXdef]
      field_simp
    have hlt : ∏ w : InfinitePlace E, w (l - l') ^ 2 < ∏ w : InfinitePlace E, (2 * (ρ w / s) ^ 2) :=
      Finset.prod_lt_prod_of_nonempty
        (fun w _ => by have := (NumberField.InfinitePlace.pos_iff (w := w)).mpr hsub0; positivity)
        (fun w _ => hsmall w) Finset.univ_nonempty
    rw [hprod] at hlt
    linarith
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  have hT : (T.card : ℝ) = ((2 * (m : ℝ) + 1) ^ 2) ^ d := by
    simp only [T]
    rw [Fintype.card_piFinset]
    push_cast
    simp only [Finset.card_product, Nat.cast_mul, card_Icc_neg_self_eq m hm0]
    rw [Finset.prod_const, Finset.card_univ, ← hd, sq]
  have hm1 : (m : ℝ) < s + 1 := Int.ceil_lt_add_one s
  have h5 : 2 * (m : ℝ) + 1 ≤ 5 * s := by linarith
  have hm0' : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  calc (P.card : ℝ) ≤ T.card := by exact_mod_cast hcard
    _ = ((2 * (m : ℝ) + 1) ^ 2) ^ d := hT
    _ ≤ ((5 * s) ^ 2) ^ d := by gcongr
    _ = 25 ^ d * s ^ (2 * d) := by rw [mul_pow, mul_pow, pow_mul]; norm_num
    _ = 50 ^ d * R / N := by
        rw [hsX, hXdef, show (50 : ℝ) = 25 * 2 by norm_num, mul_pow]; ring
    _ ≤ 100 ^ d * R / N := by
        gcongr
        norm_num

theorem nat_log_floor_upper (u : ℝ) (_hu : 0 ≤ u) : u < 2 ^ (Nat.log 2 ⌊u⌋₊ + 1) := by
  have h1 : ⌊u⌋₊ < 2 ^ (Nat.log 2 ⌊u⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : u < ⌊u⌋₊ + 1 := Nat.lt_floor_add_one u
  have h3 : ((⌊u⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊u⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem min_one_inv_le (u : ℝ) (hu : 0 < u) : min 1 (1 / u) ≤ (1 / 2 : ℝ) ^ (Nat.log 2 ⌊u⌋₊) := by
  rcases lt_or_ge u 1 with h | h
  · rw [Nat.floor_eq_zero.mpr h, Nat.log_zero_right, pow_zero]
    exact min_le_left _ _
  · have hf : 0 < ⌊u⌋₊ := Nat.floor_pos.mpr h
    have h1 : 2 ^ Nat.log 2 ⌊u⌋₊ ≤ ⌊u⌋₊ := Nat.pow_log_le_self 2 hf.ne'
    have h2 : (2 : ℝ) ^ Nat.log 2 ⌊u⌋₊ ≤ u := by
      have h3 := Nat.floor_le hu.le
      have h1' : ((2 ^ Nat.log 2 ⌊u⌋₊ : ℕ) : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      linarith
    calc min 1 (1 / u) ≤ 1 / u := min_le_right _ _
      _ ≤ 1 / 2 ^ Nat.log 2 ⌊u⌋₊ := one_div_le_one_div_of_le (by positivity) h2
      _ = (1 / 2) ^ Nat.log 2 ⌊u⌋₊ := by rw [one_div_pow]

theorem geom_prod_sum {ι : Type} [Fintype ι] (T : Finset (ι → ℕ)) :
    ∑ k ∈ T, ∏ i, (1 / 2 : ℝ) ^ (k i) ≤ 2 ^ Fintype.card ι := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ∈ T, ∀ i, k i < N := by
    refine ⟨(T.sup fun k => Finset.univ.sup k) + 1, fun k hk i => ?_⟩
    have h1 : k i ≤ Finset.univ.sup k := Finset.le_sup (f := k) (Finset.mem_univ i)
    have h2 : Finset.univ.sup k ≤ T.sup fun k => Finset.univ.sup k :=
      Finset.le_sup (f := fun k => Finset.univ.sup k) hk
    omega
  have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.range N) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_range.mpr (hN k hk i)
  calc ∑ k ∈ T, ∏ i, (1 / 2 : ℝ) ^ (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun _ : ι => Finset.range N), ∏ i, (1 / 2 : ℝ) ^ (k i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
    _ = ∏ _i : ι, ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n := by rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : ι, (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
          (fun _ _ => sum_geometric_two_le N)
    _ = 2 ^ Fintype.card ι := by simp

theorem cube_sum_le (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (x : InfinitePlace E → ℝ) (hx : ∀ w, 0 < x w) (S : Finset E) (hS : ∀ l ∈ S, l ∈ b ∧ l ≠ 0) :
    ∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3 ≤
      (800 : ℝ) ^ Fintype.card (InfinitePlace E) * (∏ w, x w) ^ 2 /
        (FractionalIdeal.absNorm b : ℝ) := by
  classical
  set d := Fintype.card (InfinitePlace E) with hd
  have hN : (0 : ℝ) < (FractionalIdeal.absNorm b : ℝ) := absNorm_pos b hb
  set Q : ℝ := (∏ w, x w) ^ 2 / (FractionalIdeal.absNorm b : ℝ) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  let kf : E → InfinitePlace E → ℕ := fun l w => Nat.log 2 ⌊w l / x w⌋₊
  let G : (InfinitePlace E → ℕ) → ℝ := fun k => ∏ w, (1 / 2 : ℝ) ^ (k w)
  have hG0 : ∀ k, 0 ≤ G k := fun k => Finset.prod_nonneg fun _ _ => by positivity
  have hfac : ∀ (n : ℕ) (y : ℝ),
      (2 ^ (n + 1) * y) ^ 2 * ((1 / 2 : ℝ) ^ n) ^ 3 = 4 * y ^ 2 * (1 / 2) ^ n := by
    intro n y
    rw [one_div_pow, pow_succ]
    have : (0 : ℝ) < 2 ^ n := by positivity
    field_simp
    ring
  have hmin : ∀ l ∈ S, ∀ w, min 1 (x w / w l) ≤ (1 / 2 : ℝ) ^ (kf l w) := by
    intro l hl w
    have hwl : 0 < w l := NumberField.InfinitePlace.pos_iff.mpr (hS l hl).2
    have h := min_one_inv_le (w l / x w) (div_pos hwl (hx w))
    rwa [one_div_div] at h
  have hbox : ∀ l ∈ S, ∀ w, w l < 2 ^ (kf l w + 1) * x w := by
    intro l hl w
    have hwl : 0 < w l := NumberField.InfinitePlace.pos_iff.mpr (hS l hl).2
    have h := nat_log_floor_upper (w l / x w) (div_pos hwl (hx w)).le
    rwa [div_lt_iff₀ (hx w)] at h
  have hF : ∀ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3 ≤ G (kf l) ^ 3 := by
    intro l hl
    have hwl : ∀ w : InfinitePlace E, 0 < w l :=
      fun w => NumberField.InfinitePlace.pos_iff.mpr (hS l hl).2
    apply pow_le_pow_left₀
      (Finset.prod_nonneg fun w _ => le_min zero_le_one (div_pos (hx w) (hwl w)).le)
    exact Finset.prod_le_prod (fun w _ => le_min zero_le_one (div_pos (hx w) (hwl w)).le)
      (fun w _ => hmin l hl w)
  have hfiber : ∀ k ∈ S.image kf,
      ∑ l ∈ S with kf l = k, (∏ w, min 1 (x w / w l)) ^ 3 ≤ 4 ^ d * 100 ^ d * Q * G k := by
    intro k _
    have hcard := card_box_le b hb (fun w => 2 ^ (k w + 1) * x w)
      (fun w => by have := hx w; positivity) (S.filter fun l => kf l = k) (by
        intro l hl
        rw [Finset.mem_filter] at hl
        obtain ⟨hlS, hk⟩ := hl
        refine ⟨(hS l hlS).1, (hS l hlS).2, fun w => ?_⟩
        rw [← hk]
        exact hbox l hlS w)
    have e : (∏ w, (2 ^ (k w + 1) * x w) ^ 2) * G k ^ 3 = 4 ^ d * (∏ w, x w) ^ 2 * G k := by
      simp only [G]
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      simp only [hfac]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← hd, Finset.prod_pow]
    calc ∑ l ∈ S with kf l = k, (∏ w, min 1 (x w / w l)) ^ 3
        ≤ ∑ l ∈ S with kf l = k, G k ^ 3 := by
          apply Finset.sum_le_sum
          intro l hl
          rw [Finset.mem_filter] at hl
          rw [← hl.2]
          exact hF l hl.1
      _ = ((S.filter fun l => kf l = k).card : ℝ) * G k ^ 3 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (100 ^ d * (∏ w, (2 ^ (k w + 1) * x w) ^ 2) / (FractionalIdeal.absNorm b : ℝ)) * G k ^ 3 :=
          mul_le_mul_of_nonneg_right hcard (pow_nonneg (hG0 k) 3)
      _ = 100 ^ d * ((∏ w, (2 ^ (k w + 1) * x w) ^ 2) * G k ^ 3) / (FractionalIdeal.absNorm b : ℝ) := by
          ring
      _ = 4 ^ d * 100 ^ d * Q * G k := by
          rw [e, hQ]
          ring
  calc ∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3
      = ∑ k ∈ S.image kf, ∑ l ∈ S with kf l = k, (∏ w, min 1 (x w / w l)) ^ 3 :=
        (Finset.sum_fiberwise_of_maps_to (fun l hl => Finset.mem_image_of_mem kf hl) _).symm
    _ ≤ ∑ k ∈ S.image kf, 4 ^ d * 100 ^ d * Q * G k := Finset.sum_le_sum hfiber
    _ = 4 ^ d * 100 ^ d * Q * ∑ k ∈ S.image kf, G k := by rw [Finset.mul_sum]
    _ ≤ 4 ^ d * 100 ^ d * Q * 2 ^ d :=
        mul_le_mul_of_nonneg_left (geom_prod_sum _) (mul_nonneg (by positivity) hQ0)
    _ = 800 ^ d * (∏ w, x w) ^ 2 / (FractionalIdeal.absNorm b : ℝ) := by
        rw [hQ, show (800 : ℝ) = 4 * 100 * 2 by norm_num, mul_pow, mul_pow]
        ring

theorem min_one_rpow (a K : ℝ) (ha : 0 < a) (hK : 0 ≤ K) : min 1 (a ^ K) = (min 1 a) ^ K := by
  rcases le_or_gt a 1 with h | h
  · rw [min_eq_right h, min_eq_right (Real.rpow_le_one ha.le h hK)]
  · rw [min_eq_left h.le, Real.one_rpow, min_eq_left (Real.one_le_rpow h.le hK)]

theorem pow_rpow_comm (t y : ℝ) (ht : 0 < t) (n : ℕ) : (t ^ n) ^ y = (t ^ y) ^ n := by
  rw [← Real.rpow_natCast (t ^ y), ← Real.rpow_natCast t, ← Real.rpow_mul ht.le,
    ← Real.rpow_mul ht.le, mul_comm]

theorem smoothedSumBound : Formalism.SA.C.BoxSum := by
  refine ⟨800, ?_⟩
  intro E _ _ _ b hb x Θ Kx hx hΘ hK hΘd S hS
  set d := Fintype.card (InfinitePlace E) with hd
  have hN : (0 : ℝ) < (FractionalIdeal.absNorm b : ℝ) := absNorm_pos b hb
  have hΘ0 : 0 < Θ := by linarith
  set A : ℝ := Θ ^ d with hA
  have hA1 : 1 ≤ A := one_le_pow₀ (by linarith)
  have hA0 : 0 < A := by linarith
  have hpx : 0 < ∏ w, x w := Finset.prod_pos fun w _ => hx w
  have hsq : (∏ w, x w) ^ 2 / (FractionalIdeal.absNorm b : ℝ) = 1 / A ^ 2 := by
    rw [hΘd, div_pow, Real.sq_sqrt hN.le, one_div_div]
  have hinvA : 1 / A = (∏ w, x w) / √(FractionalIdeal.absNorm b : ℝ) := by
    rw [hΘd, one_div_div]
  have hterm : ∀ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx) ≤
      (∏ w, min 1 (x w / w l)) ^ 3 * (1 / A) ^ (Kx - 3) := by
    intro l hl
    have hwl : ∀ w : InfinitePlace E, 0 < w l :=
      fun w => NumberField.InfinitePlace.pos_iff.mpr (hS l hl).2
    have hm0 : ∀ w, 0 ≤ min 1 (x w / w l) :=
      fun w => le_min zero_le_one (div_pos (hx w) (hwl w)).le
    have hp0 : 0 < ∏ w, min 1 (x w / w l) :=
      Finset.prod_pos fun w _ => lt_min one_pos (div_pos (hx w) (hwl w))
    have e1 : ∏ w, min 1 ((x w / w l) ^ Kx) = (∏ w, min 1 (x w / w l)) ^ Kx := by
      rw [← Real.finset_prod_rpow _ _ (fun w _ => hm0 w)]
      refine Finset.prod_congr rfl fun w _ => ?_
      exact min_one_rpow _ _ (div_pos (hx w) (hwl w)) (by linarith)
    have hpA : ∏ w, min 1 (x w / w l) ≤ 1 / A := by
      have h1 : ∏ w, min 1 (x w / w l) ≤ ∏ w, (x w / w l) :=
        Finset.prod_le_prod (fun w _ => hm0 w) (fun w _ => min_le_right _ _)
      rw [Finset.prod_div_distrib] at h1
      have h3 := sqrt_absNorm_le_prod b hb l (hS l hl).1 (hS l hl).2
      rw [hinvA]
      calc ∏ w, min 1 (x w / w l) ≤ (∏ w, x w) / ∏ w : InfinitePlace E, w l := h1
        _ ≤ (∏ w, x w) / √(FractionalIdeal.absNorm b : ℝ) :=
            div_le_div_of_nonneg_left hpx.le (Real.sqrt_pos.mpr hN) h3
    have e2 : (∏ w, min 1 (x w / w l)) ^ Kx =
        (∏ w, min 1 (x w / w l)) ^ ((3 : ℕ) : ℝ) * (∏ w, min 1 (x w / w l)) ^ (Kx - 3) := by
      rw [← Real.rpow_add hp0]
      congr 1
      push_cast
      ring
    rw [e1, e2, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp0.le hpA (by linarith)) (by positivity)
  have e : 1 / A ^ 2 * (1 / A) ^ (Kx - 3) = A ^ (-(Kx - 1)) := by
    rw [show -(Kx - 1) = (-2 : ℝ) + -(Kx - 3) by ring, Real.rpow_add hA0, Real.rpow_neg hA0.le,
      Real.rpow_neg hA0.le, one_div, one_div, Real.inv_rpow hA0.le, Real.rpow_two]
  calc ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx)
      ≤ ∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3 * (1 / A) ^ (Kx - 3) := Finset.sum_le_sum hterm
    _ = (∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3) * (1 / A) ^ (Kx - 3) := by rw [Finset.sum_mul]
    _ ≤ (800 ^ d * (∏ w, x w) ^ 2 / (FractionalIdeal.absNorm b : ℝ)) * (1 / A) ^ (Kx - 3) :=
        mul_le_mul_of_nonneg_right (cube_sum_le b hb x hx S hS) (by positivity)
    _ = 800 ^ d * A ^ (-(Kx - 1)) := by
        rw [mul_div_assoc, hsq, mul_assoc, e]
    _ ≤ 800 ^ d * A ^ (-(Kx - 5 / 2)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)) (by positivity)
    _ = (800 * Θ ^ (-(Kx - 5 / 2))) ^ d := by
        rw [mul_pow, hA, pow_rpow_comm Θ _ hΘ0]

end Formalism.SA.P
