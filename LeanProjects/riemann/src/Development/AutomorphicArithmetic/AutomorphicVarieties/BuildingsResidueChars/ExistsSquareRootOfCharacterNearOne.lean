import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem add_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

private theorem sub_eq (h2 : ‖(2 : K)‖ = 1) {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    ‖a - b‖ = ‖a ^ 2 - b ^ 2‖ := by
  have h := add_lt ha hb
  have h1 : ‖a + b‖ = 1 := by
    have e : a + b = 2 + ((a - 1) + (b - 1)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2]; exact h.ne'), h2]
    exact max_eq_left h.le
  have e : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by ring
  rw [e, norm_mul, h1, one_mul]

private theorem mul_lt {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) : ‖a * b - 1‖ < 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  rw [e]
  refine add_lt ?_ (add_lt ha hb)
  rw [norm_mul]
  nlinarith [norm_nonneg (a - 1), norm_nonneg (b - 1)]

omit [IsUltrametricDist K] in
private theorem ex_root [IsAlgClosed K] (y : Kˣ) (hy : ‖(y : K) - 1‖ < 1) :
    ∃ x : Kˣ, x ^ 2 = y ∧ ‖(x : K) - 1‖ < 1 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (y : K) (n := 2) (by norm_num)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hx]; ring)
  by_cases h : ‖x - 1‖ < 1
  · exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx), h⟩
  · refine ⟨Units.mk0 (-x) (neg_ne_zero.mpr hx0), Units.ext (by simpa using hx), ?_⟩
    have e : (y : K) - 1 = -((x - 1) * (-x - 1)) := by rw [← hx]; ring
    rw [e, norm_neg, norm_mul] at hy
    simp only [Units.val_mk0]
    by_contra h'
    push Not at h h'
    nlinarith

end

theorem UpperTheory.exists_square_root_of_character_near_one :
    UpperTheory.V.Sd.S2.SqrtChar := by
  intro l _ hl Γ _ _ η hη hc
  have h2 : ‖(2 : PadicAlgCl l)‖ = 1 := by
    have e : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
      rw [map_natCast]; norm_num
    rw [e]
    erw [PadicAlgCl.norm_extends]
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).mpr hl
  have hc' : ∀ g, ‖((η g : (PadicAlgCl l)ˣ) : PadicAlgCl l) - 1‖ < 1 := fun g => by
    simpa [UpperTheory.V.Sd.Cong] using hc g
  choose d hd hd1 using fun g => ex_root (η g) (hc' g)
  have hv : ∀ g, ((d g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ 2 = η g := fun g => by
    rw [← hd g]; simp
  have hmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    apply Units.ext
    have := sub_eq h2 (hd1 (g * h)) (mul_lt (hd1 g) (hd1 h))
    rw [mul_pow, hv, hv, hv, map_mul, Units.val_mul, sub_self, norm_zero, norm_eq_zero, sub_eq_zero] at this
    simpa using this
  refine ⟨MonoidHom.mk' d hmul, ?_, hd, fun g => ?_⟩
  · rw [Units.isEmbedding_val₀.continuous_iff]
    have hη' : Continuous fun g => ((η g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := Units.continuous_val.comp hη
    rw [continuous_iff_continuousAt]
    intro g
    have h1 := (hη'.continuousAt (x := g))
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
    refine h1.congr fun x => ?_
    simp only [Function.comp, MonoidHom.mk'_apply]
    rw [sub_eq h2 (hd1 x) (hd1 g), hv, hv]
  · simpa [UpperTheory.V.Sd.Cong] using hd1 g
