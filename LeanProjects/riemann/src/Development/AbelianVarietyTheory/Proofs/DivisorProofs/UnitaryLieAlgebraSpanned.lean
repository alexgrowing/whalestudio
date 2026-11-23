import Mathlib
open Matrix

namespace GlobalTheory.TracelessSkewSpan

variable {r : ℕ}

noncomputable def skewSub (A : Matrix (Fin r) (Fin r) ℂ) :
    Submodule ℝ (Matrix (Fin r) (Fin r) ℂ) where
  carrier := {Y | Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    have h : (X + Y).map (starRingEnd ℂ) = X.map (starRingEnd ℂ) + Y.map (starRingEnd ℂ) := by
      ext i j; simp
    rw [transpose_add, h, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᵀ * A + A * X.map (starRingEnd ℂ)) + (Yᵀ * A + A * Y.map (starRingEnd ℂ)) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c Y hY
    simp only [Set.mem_setOf_eq] at *
    have h1 : (c • Y).map (starRingEnd ℂ) = c • Y.map (starRingEnd ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [transpose_smul, h1, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]

lemma mem_skewSub {A Y : Matrix (Fin r) (Fin r) ℂ} :
    Y ∈ skewSub A ↔ Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0 := Iff.rfl

lemma eq_zero_of_mem_of_I_smul_mem {A Y : Matrix (Fin r) (Fin r) ℂ} (hA : A.det ≠ 0)
    (h1 : Y ∈ skewSub A) (h2 : Complex.I • Y ∈ skewSub A) : Y = 0 := by
  rw [mem_skewSub] at h1 h2
  have hc : (Complex.I • Y).map (starRingEnd ℂ) = (-Complex.I) • Y.map (starRingEnd ℂ) := by
    ext i j; simp
  rw [transpose_smul, hc, Matrix.smul_mul, Matrix.mul_smul] at h2
  have h3 : Yᵀ * A - A * Y.map (starRingEnd ℂ) = 0 := by
    have : Complex.I • (Yᵀ * A - A * Y.map (starRingEnd ℂ)) = 0 := by
      rw [smul_sub, ← h2, neg_smul]; abel
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  have h4 : Yᵀ * A = 0 := by
    have : (2 : ℂ) • (Yᵀ * A) = 0 := by
      rw [two_smul]
      calc Yᵀ * A + Yᵀ * A = (Yᵀ * A + A * Y.map (starRingEnd ℂ)) + (Yᵀ * A - A * Y.map (starRingEnd ℂ)) := by abel
        _ = 0 := by rw [h1, h3, add_zero]
    rcases smul_eq_zero.mp this with h | h
    · norm_num at h
    · exact h
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have h5 : Yᵀ = 0 := by
    calc Yᵀ = Yᵀ * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
      _ = 0 := by rw [h4, Matrix.zero_mul]
  simpa using congrArg Matrix.transpose h5

lemma finrank_skewSub_mul_two_le {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.det ≠ 0) :
    2 * Module.finrank ℝ (skewSub A) ≤ 2 * (r * r) := by
  set u := skewSub A
  let f : (u × u) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ :=
    u.subtype ∘ₗ LinearMap.fst ℝ u u + (Complex.I • LinearMap.id) ∘ₗ u.subtype ∘ₗ LinearMap.snd ℝ u u
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hab' : (a : Matrix (Fin r) (Fin r) ℂ) + Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = 0 := by
      simpa [f] using hab
    have hIb : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) ∈ u := by
      have : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = -(a : Matrix (Fin r) (Fin r) ℂ) :=
        eq_neg_of_add_eq_zero_right hab'
      rw [this]; exact u.neg_mem a.2
    have hb : (b : Matrix (Fin r) (Fin r) ℂ) = 0 := eq_zero_of_mem_of_I_smul_mem hA b.2 hIb
    have ha : (a : Matrix (Fin r) (Fin r) ℂ) = 0 := by simpa [hb] using hab'
    ext1
    · exact Subtype.ext ha
    · exact Subtype.ext hb
  have := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex] at this
  simp only [Fintype.card_fin] at this
  linarith

theorem mem_span_of_linearIndependent {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.det ≠ 0)
    (v : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ) (hv : LinearIndependent ℝ v)
    (hvu : ∀ i, (v i)ᵀ * A + A * (v i).map (starRingEnd ℂ) = 0 ∧ (v i).trace = 0)
    (Y : Matrix (Fin r) (Fin r) ℂ) (hY : Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0)
    (hYt : Y.trace = 0) : Y ∈ Submodule.span ℝ (Set.range v) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have : Y = 0 := Subsingleton.elim _ _
    rw [this]; exact Submodule.zero_mem _
  set u := skewSub A
  set su := u ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin r) ℂ ℂ).restrictScalars ℝ)
  have hYsu : Y ∈ su := ⟨hY, by simpa using hYt⟩
  have hle : Submodule.span ℝ (Set.range v) ≤ su := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hvu i).1, by simpa using (hvu i).2⟩
  have hIu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∈ u := by
    rw [mem_skewSub]
    have hc : (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)).map (starRingEnd ℂ)
        = (-Complex.I) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, neg_smul, add_neg_cancel]
  have hIsu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∉ su := by
    rintro ⟨-, h⟩
    have h' : Matrix.trace (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)) = 0 := by simpa using h
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at h'
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact Complex.I_ne_zero h''
    · exact absurd (by exact_mod_cast h'' : r = 0) hr.ne'
  have hlt : su < u := lt_of_le_of_ne inf_le_left (fun h => hIsu (h ▸ hIu))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : 2 * Module.finrank ℝ u ≤ 2 * (r * r) := finrank_skewSub_mul_two_le hA
  have hspan := finrank_span_eq_card hv
  rw [Fintype.card_fin] at hspan
  have heq : Submodule.span ℝ (Set.range v) = su := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hspan, sq]
    change Module.finrank ℝ su ≤ r * r - 1
    generalize r * r = n at h2 ⊢
    omega
  rw [heq]; exact hYsu

end GlobalTheory.TracelessSkewSpan
