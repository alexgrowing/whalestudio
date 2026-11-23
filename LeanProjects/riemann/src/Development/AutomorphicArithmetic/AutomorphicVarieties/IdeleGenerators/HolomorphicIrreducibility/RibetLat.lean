import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleInvariant

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd

private theorem diag2 {k : Type} [Field k] (M : GL (Fin 2) k) (α β : k) (hne : α ≠ β)
    (ht : M 0 0 + M 1 1 = α + β) (hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = α * β) :
    ∃ g : GL (Fin 2) k, (g * M * g⁻¹) 0 1 = 0 ∧ (g * M * g⁻¹) 1 0 = 0 ∧ (g * M * g⁻¹) 0 0 = α ∧ (g * M * g⁻¹) 1 1 = β := by
  have ev : ∀ x : k, x * x - (α + β) * x + α * β = 0 → ∃ v : Fin 2 → k, v ≠ 0 ∧
      M 0 0 * v 0 + M 0 1 * v 1 = x * v 0 ∧ M 1 0 * v 0 + M 1 1 * v 1 = x * v 1 := by
    intro x hx
    have : ((M : Matrix (Fin 2) (Fin 2) k) - x • 1).det = 0 := by
      rw [Matrix.det_fin_two]
      simp
      linear_combination hx + hd - x * ht
    obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.2 this
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    exact ⟨v, hv, by linear_combination h0, by linear_combination h1⟩
  obtain ⟨v, hv, v0, v1⟩ := ev α (by ring)
  obtain ⟨w, hw, w0, w1⟩ := ev β (by ring)
  have hs : α - β ≠ 0 := sub_ne_zero.2 hne
  have hdet : (!![v 0, w 0; v 1, w 1] : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    intro h
    have a00 : v 0 * w 0 = 0 := by
      apply mul_left_cancel₀ hs; linear_combination v 0 * w0 - w 0 * v0 - M 0 1 * h
    have a11 : v 1 * w 1 = 0 := by
      apply mul_left_cancel₀ hs; linear_combination v 1 * w1 - w 1 * v1 + M 1 0 * h
    have a01 : v 0 * w 1 = 0 := by
      apply mul_left_cancel₀ hs; linear_combination v 1 * w0 - w 1 * v0 + (M 0 0 - β) * h
    have a10 : v 1 * w 0 = 0 := by linear_combination a01 - h
    apply hv
    ext i
    by_contra hi
    apply hw
    fin_cases i <;> ext j <;> fin_cases j <;> simp_all
  let P : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hP : (P : Matrix (Fin 2) (Fin 2) k) = !![v 0, w 0; v 1, w 1] := rfl
  have key : (M : Matrix (Fin 2) (Fin 2) k) * P = P * !![α, 0; 0, β] := by
    rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination v0
    · linear_combination w0
    · linear_combination v1
    · linear_combination w1
  have : ((P⁻¹ * M * P⁻¹⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![α, 0; 0, β] := by
    rw [inv_inv, Units.val_mul, Units.val_mul, mul_assoc, key, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨P⁻¹, ?_, ?_, ?_, ?_⟩ <;> rw [this] <;> simp

private theorem exists_ne {Γ k : Type} [Group Γ] [Field k] (ρ : Γ →* GL (Fin 2) k) (h : IsIrr ρ) (g : GL (Fin 2) k) :
    ∃ s, (g * ρ s * g⁻¹) 0 1 ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.IrreducibleInvariant.exists_ne ρ h g

section
variable {k : Type} [NormedField k] [IsUltrametricDist k]

private theorem nadd {x y : k} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

private theorem nsub {x y : k} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]; exact nadd hx (by rwa [norm_neg])

private theorem nmul {x y : k} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right hx (norm_nonneg _) hy

private theorem nle {x y : k} (hy : ‖y‖ = 1) (h : ‖x - y‖ < 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.le hy.le)

private theorem roots [IsAlgClosed k] (t d a b : k) (ha : ‖a‖ = 1) (ht : ‖t - (a + b)‖ < 1) (hd : ‖d - a * b‖ < 1) :
    ∃ α β : k, t = α + β ∧ d = α * β ∧ ‖α - a‖ < 1 ∧ ‖β - b‖ < 1 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 2 - C t * X + C d : k[X]) (by
    have : (X ^ 2 - C t * X + C d : k[X]).degree = 2 := by compute_degree!
    rw [this]; decide)
  have hx' : d = x * (t - x) := by
    simp at hx; linear_combination hx
  have h1 : ‖(x - a) * (t - x - a)‖ < 1 := by
    have : (x - a) * (t - x - a) = (d - a * b) - a * (t - (a + b)) := by rw [hx']; ring
    rw [this]; exact nsub hd (nmul ha.le ht)
  have h2 : ‖x - a‖ < 1 ∨ ‖t - x - a‖ < 1 := by
    by_contra hc
    push Not at hc
    rw [norm_mul] at h1
    exact absurd (one_le_mul_of_one_le_of_one_le hc.1 hc.2) (not_le.2 h1)
  rcases h2 with h | h
  · refine ⟨x, t - x, by ring, hx', h, ?_⟩
    have : t - x - b = (t - (a + b)) - (x - a) := by ring
    rw [this]; exact nsub ht h
  · refine ⟨t - x, x, by ring, by rw [hx']; ring, h, ?_⟩
    have : x - b = (t - (a + b)) - (t - x - a) := by ring
    rw [this]; exact nsub ht h

private theorem core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (σ : Γ →* GL (Fin 2) k) (a b : Γ →* kˣ)
    (hc : Continuous σ) (hne : ∃ s, σ s 0 1 ≠ 0) (hab : ∀ s, ‖(a s : k)‖ = 1 ∧ ‖(b s : k)‖ = 1)
    (htr : ∀ s, ‖σ s 0 0 + σ s 1 1 - (a s + b s)‖ < 1) (g₀ : Γ) (hg : ¬ ‖(a g₀ : k) - b g₀‖ < 1)
    (h01 : σ g₀ 0 1 = 0) (h10 : σ g₀ 1 0 = 0) (h00 : ‖σ g₀ 0 0 - a g₀‖ < 1) (h11 : ‖σ g₀ 1 1 - b g₀‖ < 1) :
    ∃ g : GL (Fin 2) k, (g * σ g₀ * g⁻¹) 0 1 = 0 ∧ (g * σ g₀ * g⁻¹) 1 0 = 0 ∧
      (∀ s, ‖(g * σ s * g⁻¹) 0 0 - a s‖ < 1 ∧ ‖(g * σ s * g⁻¹) 1 1 - b s‖ < 1 ∧ ‖(g * σ s * g⁻¹) 1 0‖ < 1 ∧
        ‖(g * σ s * g⁻¹) 0 1‖ ≤ 1) ∧ ∃ s, ‖(g * σ s * g⁻¹) 0 1‖ = 1 := by
  have hmul : ∀ s t i j, σ (s * t) i j = σ s i 0 * σ t 0 j + σ s i 1 * σ t 1 j := by
    intro s t i j
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hβ : ‖σ g₀ 1 1‖ ≤ 1 := nle (hab g₀).2 h11
  have hαβ : 1 ≤ ‖σ g₀ 0 0 - σ g₀ 1 1‖ := by
    by_contra h
    apply hg
    have : (a g₀ : k) - b g₀ = (σ g₀ 0 0 - σ g₀ 1 1) - (σ g₀ 0 0 - a g₀) + (σ g₀ 1 1 - b g₀) := by ring
    rw [this]; exact nadd (nsub (not_le.1 h) h00) h11
  have hA : ∀ s, ‖σ s 0 0 - a s‖ < 1 := by
    intro s
    have h1 := htr (g₀ * s)
    rw [hmul, hmul, h01, h10, map_mul, map_mul, Units.val_mul, Units.val_mul] at h1
    have h2 : (σ g₀ 0 0 - σ g₀ 1 1) * (σ s 0 0 - a s) =
        (σ g₀ 0 0 * σ s 0 0 + 0 * σ s 1 0 + (0 * σ s 0 1 + σ g₀ 1 1 * σ s 1 1) - (a g₀ * a s + b g₀ * b s))
        - σ g₀ 1 1 * (σ s 0 0 + σ s 1 1 - (a s + b s)) - a s * (σ g₀ 0 0 - a g₀) - b s * (σ g₀ 1 1 - b g₀) := by ring
    have h3 : ‖(σ g₀ 0 0 - σ g₀ 1 1) * (σ s 0 0 - a s)‖ < 1 := by
      rw [h2]
      exact nsub (nsub (nsub h1 (nmul hβ (htr s))) (nmul (hab s).1.le h00)) (nmul (hab s).2.le h11)
    rw [norm_mul] at h3
    exact (le_mul_of_one_le_left (norm_nonneg _) hαβ).trans_lt h3
  have hD : ∀ s, ‖σ s 1 1 - b s‖ < 1 := by
    intro s
    have : σ s 1 1 - b s = (σ s 0 0 + σ s 1 1 - (a s + b s)) - (σ s 0 0 - a s) := by ring
    rw [this]; exact nsub (htr s) (hA s)
  have hBC : ∀ s t, ‖σ s 0 1 * σ t 1 0‖ < 1 := by
    intro s t
    have h1 := hA (s * t)
    rw [hmul, map_mul, Units.val_mul] at h1
    have : σ s 0 1 * σ t 1 0 = (σ s 0 0 * σ t 0 0 + σ s 0 1 * σ t 1 0 - a s * a t) - σ s 0 0 * (σ t 0 0 - a t)
      - a t * (σ s 0 0 - a s) := by ring
    rw [this]
    exact nsub (nsub h1 (nmul (nle (hab s).1 (hA s)) (hA t))) (nmul (hab t).1.le (hA s))
  have hcB : Continuous fun s => ‖σ s 0 1‖ :=
    ((Units.continuous_val.comp hc).matrix_elem 0 1).norm
  obtain ⟨s₀, -, hs₀⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hcB.continuousOn
  have hmax : ∀ s, ‖σ s 0 1‖ ≤ ‖σ s₀ 0 1‖ := fun s => hs₀ (Set.mem_univ s)
  obtain ⟨s₁, hs₁⟩ := hne
  have hpos : 0 < ‖σ s₀ 0 1‖ := (norm_pos_iff.2 hs₁).trans_le (hmax s₁)
  have hB : σ s₀ 0 1 ≠ 0 := norm_pos_iff.1 hpos
  set B := σ s₀ 0 1 with hBdef
  let g : GL (Fin 2) k := ⟨!![1, 0; 0, B], !![1, 0; 0, B⁻¹], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hB], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hB]⟩
  have hgv : ∀ s, ((g * σ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![σ s 0 0, σ s 0 1 * B⁻¹; B * σ s 1 0, σ s 1 1] := by
    intro s
    show !![1, 0; 0, B] * (σ s : Matrix (Fin 2) (Fin 2) k) * !![1, 0; 0, B⁻¹] = _
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  refine ⟨g, ?_, ?_, fun s => ⟨?_, ?_, ?_, ?_⟩, s₀, ?_⟩ <;> rw [hgv]
  · simp [h01]
  · simp [h10]
  · exact hA s
  · exact hD s
  · exact hBC s₀ s
  · show ‖σ s 0 1 * B⁻¹‖ ≤ 1
    rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_le_one hpos]; exact hmax s
  · show ‖B * B⁻¹‖ = 1
    rw [mul_inv_cancel₀ hB, norm_one]

end

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.ribetLat :
    UpperTheory.V.Sd.RibetLat := by
  intro l _ Γ _ _ _ _ _ ρ a b hc hirr hab hres g₀ hg
  have hprod : ∀ s, (∏ j, (X - C ((![a, b] j s : (Qbar l)ˣ) : Qbar l))) =
      X ^ 2 - C ((a s : Qbar l) + b s) * X + C ((a s : Qbar l) * b s) := by
    intro s
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul]
    ring
  have htr : ∀ s, ‖(ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (a s + b s)‖ < 1 := by
    intro s
    have := hres s 1
    rw [hprod, Matrix.charpoly_fin_two] at this
    simp only [coeff_add, coeff_sub, coeff_C_mul_X, coeff_X_pow, coeff_C] at this
    norm_num only [if_true, if_false, reduceIte] at this
    rw [← norm_neg]
    refine lt_of_eq_of_lt (congrArg _ ?_) this
    ring
  have hdet : ‖(ρ g₀ : Matrix (Fin 2) (Fin 2) (Qbar l)).det - a g₀ * b g₀‖ < 1 := by
    have := hres g₀ 0
    rw [hprod, Matrix.charpoly_fin_two] at this
    simp only [coeff_add, coeff_sub, coeff_C_mul_X, coeff_X_pow, coeff_C] at this
    convert this using 2
    simp
  obtain ⟨α, β, h1, h2, h3, h4⟩ := roots _ _ _ _ (hab g₀).1 (htr g₀) hdet
  have hne : α ≠ β := by
    rintro rfl
    apply hg
    have : (a g₀ : Qbar l) - b g₀ = (α - b g₀) - (α - a g₀) := by ring
    unfold Cong
    rw [this]; exact nsub h4 h3
  rw [Matrix.trace_fin_two] at h1
  rw [Matrix.det_fin_two] at h2
  obtain ⟨P, p1, p2, p3, p4⟩ := diag2 (ρ g₀) α β hne h1 h2
  let σ : Γ →* GL (Fin 2) (Qbar l) := (MulAut.conj P).toMonoidHom.comp ρ
  have hσ : ∀ s, σ s = P * ρ s * P⁻¹ := fun s => rfl
  have hσc : Continuous σ := (continuous_const.mul hc).mul continuous_const
  obtain ⟨g, q1, q2, q3, q4⟩ := core σ a b hσc (exists_ne ρ hirr P) hab (fun s => by
    rw [← Matrix.trace_fin_two, hσ, Units.val_mul, Units.val_mul, Matrix.trace_units_conj]
    exact htr s) g₀ hg p1 p2 (by rw [hσ, p3]; exact h3) (by rw [hσ, p4]; exact h4)
  refine ⟨(MulAut.conj g).toMonoidHom.comp σ, ⟨g * P, fun s => ?_⟩, q1, q2, q3, q4⟩
  show g * (P * ρ s * P⁻¹) * g⁻¹ = _
  group
