import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open scoped Pointwise

private theorem conj_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (a : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ iwahori F n)
    (h : ∀ i j, a i < a j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    torusPow F n a * g * (torusPow F n a)⁻¹ ∈ iwahori F n := by
  have he : ∀ i j, ((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) F) i j := by
    intro i j
    rw [← torusPow_neg, Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, Matrix.mul_diagonal,
      Matrix.diagonal_mul, sub_eq_add_neg, zpow_add₀ (GLnLocal.uniformizer_ne_zero F), Pi.neg_apply]
    ring
  have hle : ∀ i j, ValuativeRel.valuation F
      (((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ≤
      ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j) := by
    intro i j
    rw [he]
    rcases lt_or_ge (a i) (a j) with hij | hij
    · rw [h i j hij, mul_zero]
    · simpa using Parabolic.valuation_zpow_mul_le_pow_mul (F := F) (e := 0) (z := a i - a j)
        (x := (g : Matrix (Fin n) (Fin n) F) i j) (by simpa using hij)
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hg
  refine (mem_iwahori_iff F n).2 ⟨fun i j => (hle i j).trans (h1 i j),
    fun i j hij => (hle i j).trans_lt (h2 i j hij), fun i => ?_⟩
  rw [he, sub_self, zpow_zero, one_mul, h3]

private theorem fact {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    {k : GL (Fin n) F} (hk : k ∈ iwahori F n) :
    ∃ u ∈ unipotent F n, u ∈ iwahori F n ∧ ∃ w, k = u * w ∧
      ∀ b : Fin n → ℤ, Antitone b → (torusPow F n b)⁻¹ * w * torusPow F n b ∈ iwahori F n := by
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id k hk
  have hx' := Parabolic.mem_unipotentRadical.1 hx.2
  refine ⟨x, (mem_unipotent F n).2 ⟨hx'.1, fun i => by simpa using hx'.2 i i rfl⟩, hx.1, y * z, mul_assoc _ _ _,
    fun b hb => ?_⟩
  have h1 := conj_mem (-b) hz.1 fun i j hij =>
    (Parabolic.mem_oppositeUnipotentRadical.1 hz.2).1 i j
      (lt_of_not_ge fun h => (hb h).not_gt (neg_lt_neg_iff.1 hij))
  have h2 := conj_mem (-b) hy.1 fun i j hij =>
    Parabolic.mem_levi.1 hy.2 i j (fun h => by
      have h' : i = j := h
      subst h'; exact lt_irrefl _ hij)
  rw [torusPow_neg, inv_inv] at h1 h2
  have := mul_mem h2 h1
  simpa [mul_assoc] using this

theorem UpperTheory.ConvolutionTheory.H.dcoShape :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (a : Fin n → ℤ), Antitone a →
      (∀ g, g ∈ dco F a ↔ ∃ u ∈ unipotent F n ⊓ integralGL F n, ∃ y ∈ iwahori F n, g = u * torusPow F n a * y) ∧
      (∀ b, Antitone b → ∀ g ∈ dco F a, ∀ g' ∈ dco F b, g * g' ∈ dco F (a + b)) ∧
      uFn F a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ ∧ BiI F (uFn F a) := by
  intro F _ _ _ _ n a ha
  have hbi : ∀ g, ∀ y ∈ iwahori F n, (y * g ∈ dco F a ↔ g ∈ dco F a) ∧ (g * y ∈ dco F a ↔ g ∈ dco F a) := by
    have hl : ∀ g, ∀ y ∈ iwahori F n, g ∈ dco F a → y * g ∈ dco F a := by
      rintro g y hy ⟨x, hx, x', hx', rfl⟩
      exact ⟨y * x, mul_mem hy hx, x', hx', by group⟩
    have hr : ∀ g, ∀ y ∈ iwahori F n, g ∈ dco F a → g * y ∈ dco F a := by
      rintro g y hy ⟨x, hx, x', hx', rfl⟩
      exact ⟨x, hx, x' * y, mul_mem hx' hy, by group⟩
    intro g y hy
    exact ⟨⟨fun h => by simpa using hl _ _ (inv_mem hy) h, hl g y hy⟩,
      ⟨fun h => by simpa using hr _ _ (inv_mem hy) h, hr g y hy⟩⟩
  refine ⟨fun g => ⟨?_, ?_⟩, ?_, ?_, fun g y hy => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk, y, hy, rfl⟩
    obtain ⟨u, hu, huI, w, rfl, hw⟩ := fact hk
    exact ⟨u, ⟨hu, iwahori_le_integralGL F n huI⟩, _, mul_mem (hw a ha) hy, by group⟩
  · rintro ⟨u, ⟨hu, hu'⟩, y, hy, rfl⟩
    refine ⟨u, ?_, y, hy, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_unipotent F n).1 hu
    refine (mem_iwahori_iff F n).2 ⟨fun i j => ((mem_integralGL_iff F n).1 hu').1 i j, fun i j hij => ?_, fun i => ?_⟩
    · rw [h1 hij, map_zero]; exact zero_lt_one
    · rw [h2, map_one]
  · rintro b hb g ⟨x, hx, y, hy, rfl⟩ g' ⟨x', hx', y', hy', rfl⟩
    obtain ⟨u, hu, huI, w, e, hw⟩ := fact (mul_mem hy hx')
    have h1 := conj_mem a huI fun i j hij =>
      ((mem_unipotent F n).1 hu).1 (lt_of_not_ge fun h => (ha h).not_gt hij)
    refine ⟨_, mul_mem hx h1, _, mul_mem (hw b hb) hy', ?_⟩
    rw [torusPow_add]
    calc x * torusPow F n a * y * (x' * torusPow F n b * y')
        = x * torusPow F n a * (y * x') * torusPow F n b * y' := by group
      _ = _ := by rw [e]; group
  · have e : dco F a = (iwahori F n : Set (GL (Fin n) F)) * {torusPow F n a} * (iwahori F n : Set (GL (Fin n) F)) := by
      ext g
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact Set.mul_mem_mul (Set.mul_mem_mul hx rfl) hy
      · rintro ⟨_, ⟨x, hx, _, rfl, rfl⟩, y, hy, rfl⟩
        exact ⟨x, hx, y, hy, rfl⟩
    refine indicator_mem_locallyConstantCompactSupport (R := ℂ) (U := dco F a) ?_ ?_ (1 : ℂ)
    · rw [e]; exact ((isCompact_iwahori F n).mul isCompact_singleton).mul (isCompact_iwahori F n)
    · rw [e]; exact (isOpen_iwahori F n).mul_left
  · by_cases h : g ∈ dco F a
    · simp [uFn, h, (hbi g y hy).1]
    · simp [uFn, h, (hbi g y hy).1]
  · by_cases h : g ∈ dco F a
    · simp [uFn, h, (hbi g y hy).2]
    · simp [uFn, h, (hbi g y hy).2]
