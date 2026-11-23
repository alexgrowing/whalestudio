import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd.S2 GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem um_add_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

private theorem um_add_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem um_sub_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]; exact um_add_lt ha (by rwa [norm_neg])

private theorem um_sub_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact um_add_le ha (by rwa [norm_neg])

private theorem le_of_cong {a x : K} (h : ‖a - x‖ < 1) (hx : ‖x‖ = 1) : ‖a‖ ≤ 1 := by
  have := um_add_le h.le hx.le
  rwa [sub_add_cancel] at this

private theorem diff_lt {a b x : K} (ha : ‖a - x‖ < 1) (hb : ‖b - x‖ < 1) : ‖a - b‖ < 1 := by
  have := um_sub_lt ha hb
  rwa [sub_sub_sub_cancel_right] at this

private theorem half_lt (h2 : ‖(2 : K)‖ = 1) {a b x : K} (ha : ‖a - x‖ < 1) (hb : ‖b - x‖ < 1) :
    ‖(2 : K)⁻¹ * (a + b) - x‖ < 1 := by
  have h0 : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact zero_ne_one h2
  have e : (2 : K)⁻¹ * (a + b) - x = (2 : K)⁻¹ * ((a - x) + (b - x)) := by
    field_simp; ring
  rw [e, norm_mul, norm_inv, h2, inv_one, one_mul]
  exact um_add_lt ha hb

private theorem key (h2 : ‖(2 : K)‖ = 1) (γ : Kˣ) (x : K) (A B : Matrix (Fin 2) (Fin 2) K) (hγ : ‖(γ : K)‖ = 1) (hx : ‖x‖ = 1)
    (a00 : ‖A 0 0 - 1‖ < 1) (a11 : ‖A 1 1 - x‖ < 1) (a10 : ‖A 1 0‖ < 1) (a01 : ‖A 0 1‖ ≤ 1)
    (b00 : ‖B 0 0 - 1‖ < 1) (b11 : ‖B 1 1 - x‖ < 1) (b10 : ‖B 1 0‖ < 1) (b01 : ‖B 0 1‖ ≤ 1) :
    (∀ i j, ‖mix γ A B i j‖ ≤ 1) ∧ (∀ i, ‖mix γ A B i i - ![x, 1, x, 1] i‖ < 1) ∧
    (∀ i j, i ≠ j → wt i j ∉ vV → ‖mix γ A B i j‖ < 1) ∧
    (‖A 0 1‖ = 1 → ‖mix γ A B 1 0‖ = 1 ∨ (‖mix γ A B 1 2‖ = 1 ∧ ‖mix γ A B 3 0‖ = 1)) := by
  have hh : ∀ y : K, ‖(2 : K)⁻¹ * y‖ = ‖y‖ := fun y => by rw [norm_mul, norm_inv, h2, inv_one, one_mul]
  have h0 : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact zero_ne_one h2
  have p : ‖A 1 0 / γ‖ < 1 := by rwa [norm_div, hγ, div_one]
  have p' : ‖-(A 1 0 / γ)‖ < 1 := by rwa [norm_neg]
  have qe : ‖γ * A 0 1‖ = ‖A 0 1‖ := by rw [norm_mul, hγ, one_mul]
  have q : ‖γ * A 0 1‖ ≤ 1 := qe ▸ a01
  have q' : ‖-(γ * A 0 1)‖ ≤ 1 := by rwa [norm_neg]
  have c00 := le_of_cong a00 norm_one
  have c11 := le_of_cong a11 hx
  have d00 := le_of_cong b00 norm_one
  have d11 := le_of_cong b11 hx
  have e01 : ‖mix γ A B 0 1‖ < 1 := (hh _).trans_lt (um_sub_lt p b10)
  have e02 : ‖mix γ A B 0 2‖ < 1 := (hh _).trans_lt (diff_lt b11 a11)
  have e03 : ‖mix γ A B 0 3‖ < 1 := (hh _).trans_lt (um_add_lt p b10)
  have e13 : ‖mix γ A B 1 3‖ < 1 := (hh _).trans_lt (diff_lt a00 b00)
  have e20 : ‖mix γ A B 2 0‖ < 1 := (hh _).trans_lt (diff_lt b11 a11)
  have e21 : ‖mix γ A B 2 1‖ < 1 := (hh _).trans_lt (um_sub_lt p' b10)
  have e23 : ‖mix γ A B 2 3‖ < 1 := (hh _).trans_lt (um_add_lt p' b10)
  have e31 : ‖mix γ A B 3 1‖ < 1 := (hh _).trans_lt (diff_lt a00 b00)
  have e00 : ‖mix γ A B 0 0‖ ≤ 1 := (hh _).trans_le (um_add_le c11 d11)
  have e11 : ‖mix γ A B 1 1‖ ≤ 1 := (hh _).trans_le (um_add_le c00 d00)
  have e22 : ‖mix γ A B 2 2‖ ≤ 1 := (hh _).trans_le (um_add_le c11 d11)
  have e33 : ‖mix γ A B 3 3‖ ≤ 1 := (hh _).trans_le (um_add_le c00 d00)
  have e10 : ‖mix γ A B 1 0‖ ≤ 1 := (hh _).trans_le (um_sub_le q b01)
  have e12 : ‖mix γ A B 1 2‖ ≤ 1 := (hh _).trans_le (um_sub_le q' b01)
  have e30 : ‖mix γ A B 3 0‖ ≤ 1 := (hh _).trans_le (um_add_le q b01)
  have e32 : ‖mix γ A B 3 2‖ ≤ 1 := (hh _).trans_le (um_add_le q' b01)
  refine ⟨fun i j => ?_, fun i => ?_, fun i j hij hw => ?_, fun h => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [e00, e01.le, e02.le, e03.le, e10, e11, e12, e13.le, e20.le, e21.le, e22, e23.le, e30, e31.le, e32, e33]
  · fin_cases i
    exacts [half_lt h2 a11 b11, half_lt h2 a00 b00, half_lt h2 a11 b11, half_lt h2 a00 b00]
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact (hw (by decide)).elim
      | assumption
  · have m10 : mix γ A B 1 0 = (2 : K)⁻¹ * (γ * A 0 1 - B 0 1) := rfl
    have m12 : mix γ A B 1 2 = (2 : K)⁻¹ * (-(γ * A 0 1) - B 0 1) := rfl
    have m30 : mix γ A B 3 0 = (2 : K)⁻¹ * (γ * A 0 1 + B 0 1) := rfl
    have s : mix γ A B 1 0 + mix γ A B 3 0 = γ * A 0 1 := by
      rw [m10, m30]; field_simp; ring
    have n : ‖mix γ A B 1 2‖ = ‖mix γ A B 3 0‖ := by
      rw [← norm_neg, m12, m30]; congr 1; ring
    rcases e10.eq_or_lt with h1 | h1
    · exact Or.inl h1
    rcases e30.eq_or_lt with h3 | h3
    · exact Or.inr ⟨n.trans h3, h3⟩
    have := um_add_lt h1 h3
    rw [s, qe, h] at this
    exact absurd this (lt_irrefl _)

end

theorem UpperTheory.mixMatrix_residue_properties :
    UpperTheory.V.Sd.S2.MixRes := by
  intro l hl l2 γ x A B hγ hx hA hB
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    have e : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by
      rw [map_natCast]; rfl
    rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hl.out Nat.prime_two).2 l2
  exact key h2 γ x A B hγ hx hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
