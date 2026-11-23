import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd.S2
open scoped Matrix

section
variable {k : Type} [Field k]

private def nn (p q r s t : k) : M4 k := !![1, 0, 0, 0; p, 1, 0, 0; q, s, 1, 0; r, t, -p, 1]

private theorem adj_nn (p q r s t : k) :
    adj (nn p q r s t) = !![1, 0, 0, 0; -p, 1, 0, 0; -t, -s, 1, 0; -r, -q, p, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, nn, sgn, Fin.rev]

private theorem low_nn (p q r s t : k) (h : t + p * s - q = 0) : IsLow (nn p q r s t) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsGSp
    rw [adj_nn]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nn, Matrix.mul_apply, Fin.sum_univ_four] <;>
      first | ring1 | linear_combination h | linear_combination -h
  · intro i
    fin_cases i <;> simp [nn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [nn]

private theorem par1 (u a a' : k) (A : Matrix (Fin 2) (Fin 2) k) (ha : a ≠ 0)
    (h : A *ᵥ ![u, 1] = a • ![u, 1]) (hd : A.det = a * a') :
    ∃ p, A = !![a' + u * p, (a - a' - u * p) * u; p, a - p * u] := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hd
  have h2 : A 0 0 = a' + u * A 1 0 := by
    apply mul_left_cancel₀ ha
    linear_combination hd - A 0 0 * h1 + A 1 0 * h0
  refine ⟨A 1 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · exact h2
  · linear_combination h0 - u * h2
  · linear_combination h1

private theorem par2 (w b b' : k) (B : Matrix (Fin 2) (Fin 2) k) (hb : b ≠ 0)
    (h : B *ᵥ ![1, w] = b • ![1, w]) (hd : B.det = b * b') :
    ∃ q, B = !![b - q * w, q; (b - b' - q * w) * w, b' + q * w] := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hd
  have h2 : B 1 1 = b' + B 0 1 * w := by
    apply mul_left_cancel₀ hb
    linear_combination hd - B 1 1 * h0 + B 0 1 * h1
  refine ⟨B 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination h0
  · linear_combination h1 - w * h2
  · exact h2

private theorem case1 (h2 : (2 : k) ≠ 0) (γ : kˣ) (u w : k) (hz : 1 + γ * u * w ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) k) (a a' b b' : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : A *ᵥ ![u, 1] = a • ![u, 1]) (hB : B *ᵥ ![1, w] = b • ![1, w]) (dA : A.det = a * a') (dB : B.det = b * b')
    (n : M4 k) (hn : n = nn (γ * u) (-1) (γ * u) (-(2 * w) / (1 + γ * u * w)) (-(1 - γ * u * w) / (1 + γ * u * w))) :
    IsUp (adj n * mix γ A B * n) ∧ ∀ i, (adj n * mix γ A B * n) i i = ![a, b, b', a'] i := by
  obtain ⟨p, rfl⟩ := par1 u a a' A ha hA dA
  obtain ⟨q, rfl⟩ := par2 w b b' B hb hB dB
  have hγ : (γ : k) ≠ 0 := γ.ne_zero
  subst hn
  rw [adj_nn]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)
  · intro i
    fin_cases i <;> (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)

private theorem case2 (h2 : (2 : k) ≠ 0) (γ : kˣ) (u w : k) (hz : (γ : k) + u * w ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) k) (a a' b b' : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : A *ᵥ ![1, w] = a • ![1, w]) (hB : B *ᵥ ![u, 1] = b • ![u, 1]) (dA : A.det = a * a') (dB : B.det = b * b')
    (n : M4 k) (hn : n = nn (-u) 1 u (-(2 * w) / (γ + u * w)) ((γ - u * w) / (γ + u * w))) :
    IsUp (adj n * mix γ A B * n) ∧ ∀ i, (adj n * mix γ A B * n) i i = ![b, a, a', b'] i := by
  obtain ⟨p, rfl⟩ := par2 w a a' A ha hA dA
  obtain ⟨q, rfl⟩ := par1 u b b' B hb hB dB
  have hγ : (γ : k) ≠ 0 := γ.ne_zero
  subst hn
  rw [adj_nn]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)
  · intro i
    fin_cases i <;> (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)

end

private theorem norm_add_one {k : Type} [NormedField k] [IsUltrametricDist k] (x y : k) (hx : ‖x‖ = 1) (hy : ‖y‖ < 1) :
    ‖x + y‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hx]; exact hy.ne'), hx]
  exact max_eq_left hy.le

private theorem norm_two_mul {k : Type} [NormedField k] [IsUltrametricDist k] (w : k) (hw : ‖w‖ < 1) :
    ‖2 * w‖ < 1 := by
  rw [two_mul]
  exact (IsUltrametricDist.norm_add_le_max w w).trans_lt (by simpa using hw)

private theorem lowQ_nn {l : ℕ} [Fact l.Prime] (p q r s t : Formalism.ConjugateSelfDual.Qbar l) (h : t + p * s - q = 0)
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ = 1) (hr : ‖r‖ ≤ 1) (hs : ‖s‖ < 1) (ht : ‖t‖ ≤ 1) : LowQ (nn p q r s t) := by
  refine ⟨low_nn p q r s t h, ?_, by simpa [nn] using hs, by simpa [nn] using hq⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nn, hp, hq.le, hr, hs.le, ht]

theorem UpperTheory.mix_flag_exists :
    UpperTheory.V.Sd.S2.MixFlag := by
  intro l _ _ γ u w hγ hu hw
  have huw : ‖u * w‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans_lt hw
  have hz : ‖γ * u * w‖ < 1 := by rw [mul_assoc, norm_mul, hγ, one_mul]; exact huw
  have h1 := norm_add_one 1 _ norm_one hz
  have h1' : ‖1 - γ * u * w‖ = 1 := by
    rw [sub_eq_add_neg]; exact norm_add_one 1 _ norm_one (by rwa [norm_neg])
  have h3 := norm_add_one _ _ hγ huw
  have h3' : ‖γ - u * w‖ = 1 := by
    rw [sub_eq_add_neg]; exact norm_add_one _ _ hγ (by rwa [norm_neg])
  have n1 : 1 + γ * u * w ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have n3 : γ + u * w ≠ 0 := by
    intro h; rw [h, norm_zero] at h3; exact zero_ne_one h3
  have h2 := norm_two_mul w hw
  have hgu : ‖γ * u‖ ≤ 1 := by rw [norm_mul, hγ, one_mul]; exact hu
  refine ⟨⟨_, lowQ_nn (γ.val * u) (-1) (γ.val * u) (-(2 * w) / (1 + γ.val * u * w)) (-(1 - γ.val * u * w) / (1 + γ.val * u * w)) ?_ hgu
      (by simp) hgu ?_ ?_, fun A B a a' b b' ha hb hA hB dA dB => case1 two_ne_zero γ u w n1 A B a a' b b' ha hb hA hB dA dB _ rfl⟩,
    ⟨_, lowQ_nn (-u) 1 u (-(2 * w) / (γ.val + u * w)) ((γ.val - u * w) / (γ.val + u * w)) ?_ (by rwa [norm_neg])
      (by simp) hu ?_ ?_, fun A B a a' b b' ha hb hA hB dA dB => case2 two_ne_zero γ u w n3 A B a a' b b' ha hb hA hB dA dB _ rfl⟩⟩
  · field_simp; ring
  · rw [norm_div, norm_neg, h1, div_one]; exact h2
  · rw [norm_div, norm_neg, h1, h1', div_one]
  · field_simp; ring
  · rw [norm_div, norm_neg, h3, div_one]; exact h2
  · rw [norm_div, h3, h3', div_one]
