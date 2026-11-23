import Formalism.HermitianCurvature.StatementW

namespace Formalism.FourierDecayAlt.P.W

open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W

section Words

variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]

theorem first_embedding_mul (M N : Matrix (Fin 2) (Fin 2) B) : E1 (M * N) = E1 M * E1 N := by
  unfold Formalism.YangianSpanCharacter.T.E1
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem entries_mem_mul (M N : Matrix (Fin 2) (Fin 2) B) : E2 (M * N) = E2 M * E2 N := by
  unfold Formalism.YangianSpanCharacter.T.E2
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem first_embedding_one : E1 (1 : Matrix (Fin 2) (Fin 2) B) = 1 := by
  unfold Formalism.YangianSpanCharacter.T.E1
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem entries_mem_one : E2 (1 : Matrix (Fin 2) (Fin 2) B) = 1 := by
  unfold Formalism.YangianSpanCharacter.T.E2
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem first_second_embedding_commute (A C : Matrix (Fin 2) (Fin 2) B)
    (h : ∀ i j k l, A i j * C k l = C k l * A i j) : E1 A * E2 C = E2 C * E1 A := by
  unfold Formalism.YangianSpanCharacter.T.E1 Formalism.YangianSpanCharacter.T.E2
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, h]

theorem transpose_mul_of_comm (A C : Matrix (Fin 2) (Fin 2) B)
    (h : ∀ i j k l, A i j * C k l = C k l * A i j) : (A * C)ᵀ = Cᵀ * Aᵀ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, h]

theorem isDet_iff (M : R → Matrix (Fin 2) (Fin 2) B) (q : R → R) :
    IsDet M q ↔ ∀ Y : R, (M (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J B * M Y = q Y • Formalism.YangianSpanCharacter.T.J B ∧
      M Y * Formalism.YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J B := by
  unfold Formalism.FourierDecayAlt.W.IsDet
  simp only [algebraMap_smul]

private theorem rtt_relation_mul_of_rtt_of_commute {A : Type*} [Ring A] (P a b c d : A) (hM : P * a * c = c * a * P)
    (hN : P * b * d = d * b * P) (c1 : b * c = c * b) (c2 : a * d = d * a) :
    P * (a * b) * (c * d) = c * d * (a * b) * P := by
  calc P * (a * b) * (c * d) = P * a * (b * c) * d := by simp only [mul_assoc]
    _ = P * a * (c * b) * d := by rw [c1]
    _ = (P * a * c) * b * d := by simp only [mul_assoc]
    _ = (c * a * P) * b * d := by rw [hM]
    _ = c * a * (P * b * d) := by simp only [mul_assoc]
    _ = c * a * (d * b * P) := by rw [hN]
    _ = c * (a * d) * b * P := by simp only [mul_assoc]
    _ = c * (d * a) * b * P := by rw [c2]
    _ = c * d * (a * b) * P := by simp only [mul_assoc]

theorem isRTT_mul (M N : R → Matrix (Fin 2) (Fin 2) B) (hM : IsRTT M) (hN : IsRTT N)
    (hc : EntriesCommute M N) : IsRTT (fun Y => M Y * N Y) := by
  unfold Formalism.FourierDecayAlt.W.IsRTT at *
  intro Y Y'
  simp only [first_embedding_mul, entries_mem_mul]
  exact rtt_relation_mul_of_rtt_of_commute _ _ _ _ _ (hM Y Y') (hN Y Y')
    (first_second_embedding_commute _ _ (fun i j k l => (hc Y Y' k l i j).symm)) (first_second_embedding_commute _ _ (fun i j k l => hc Y' Y i j k l))

private theorem mul_Jm_mul_eq_smul_of_Jm_similitudes_left {A : Type*} [Ring A] [Algebra R A] (a a' b b' Jm : A) (s t : R)
    (h1 : a' * Jm * a = s • Jm) (h3 : b' * Jm * b = t • Jm) : b' * a' * Jm * (a * b) = (s * t) • Jm := by
  calc b' * a' * Jm * (a * b) = b' * (a' * Jm * a) * b := by simp only [mul_assoc]
    _ = b' * (s • Jm) * b := by rw [h1]
    _ = s • (b' * Jm * b) := by rw [mul_smul_comm, smul_mul_assoc]
    _ = s • (t • Jm) := by rw [h3]
    _ = (s * t) • Jm := by rw [smul_smul]

private theorem mul_Jm_mul_eq_smul_of_Jm_similitudes_right {A : Type*} [Ring A] [Algebra R A] (a a' b b' Jm : A) (s t : R)
    (h2 : a * Jm * a' = s • Jm) (h4 : b * Jm * b' = t • Jm) : a * b * Jm * (b' * a') = (s * t) • Jm := by
  calc a * b * Jm * (b' * a') = a * (b * Jm * b') * a' := by simp only [mul_assoc]
    _ = a * (t • Jm) * a' := by rw [h4]
    _ = t • (a * Jm * a') := by rw [mul_smul_comm, smul_mul_assoc]
    _ = t • (s • Jm) := by rw [h2]
    _ = (s * t) • Jm := by rw [smul_smul, mul_comm]

theorem isDet_mul (M N : R → Matrix (Fin 2) (Fin 2) B) (q qN : R → R) (hM : IsDet M q)
    (hN : IsDet N qN) (hc : EntriesCommute M N) :
    IsDet (fun Y => M Y * N Y) (fun Y => q Y * qN Y) := by
  rw [isDet_iff] at hM hN ⊢
  intro Y
  obtain ⟨h1, h2⟩ := hM Y
  obtain ⟨h3, h4⟩ := hN Y
  have ht := transpose_mul_of_comm (M (Y + 1)) (N (Y + 1)) (fun i j k l => hc (Y + 1) (Y + 1) i j k l)
  try beta_reduce
  refine ⟨?_, ?_⟩
  · rw [ht]
    exact mul_Jm_mul_eq_smul_of_Jm_similitudes_left _ _ _ _ _ _ _ h1 h3
  · rw [ht]
    exact mul_Jm_mul_eq_smul_of_Jm_similitudes_right _ _ _ _ _ _ _ h2 h4

theorem entriesCommute_prod (M : R → Matrix (Fin 2) (Fin 2) B)
    (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R)))
    (h : ∀ y ∈ L, EntriesCommute M y.1) :
    EntriesCommute M (fun Y => (L.map (fun x => x.1 Y)).prod) := by
  unfold Formalism.FourierDecayAlt.W.EntriesCommute at *
  intro Y Y' i j k l
  induction L generalizing k l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
    split_ifs <;> simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    have hx := h x (by simp)
    have ht : ∀ y ∈ t, ∀ (Y Y' : R) (i j k l : Fin 2), M Y i j * y.1 Y' k l = y.1 Y' k l * M Y i j :=
      fun y hy => h y (by simp [hy])
    exact (Commute.sum_right _ _ _ (fun m _ => Commute.mul_right (hx Y Y' i j k m) (ih ht m l))).eq

set_option maxHeartbeats 800000 in

theorem wordFusion_list (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R)))
    (h : ∀ x ∈ L, IsRTT x.1 ∧ IsDet x.1 x.2)
    (hp : L.Pairwise (fun x y => EntriesCommute x.1 y.1)) :
    IsRTT (fun Y => (L.map (fun x => x.1 Y)).prod) ∧
      IsDet (fun Y => (L.map (fun x => x.1 Y)).prod) (fun Y => (L.map (fun x => x.2 Y)).prod) := by
  induction L with
  | nil =>
    refine ⟨?_, ?_⟩
    · unfold Formalism.FourierDecayAlt.W.IsRTT
      intro Y Y'
      simp [first_embedding_one, entries_mem_one]
    · rw [isDet_iff]
      intro Y
      simp
  | cons x t ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ t, IsRTT y.1 ∧ IsDet y.1 y.2 := fun y hy => h y (by simp [hy])
    rw [List.pairwise_cons] at hp
    obtain ⟨ih1, ih2⟩ := ih ht hp.2
    have hc := entriesCommute_prod x.1 t hp.1
    have e1 := isRTT_mul x.1 _ hx.1 ih1 hc
    have e2 := isDet_mul x.1 _ x.2 _ hx.2 ih2 hc
    simp only [List.map_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · first
      | exact e1
      | simpa using e1
    · first
      | exact e2
      | simpa using e2

end Words

section Norm

theorem absNorm_le_norm {E : Type} [Field E] [NumberField E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ |(Algebra.norm ℚ l : ℝ)| := by
  have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ b :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hl
  have hs0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hl0
  have hbc : b * (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l := by
    rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  have hc1 : b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ 1 := by
    calc b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ b⁻¹ * b := by
          first
          | exact FractionalIdeal.mul_left_mono _ hsp
          | exact mul_le_mul_left' hsp _
          | exact mul_le_mul' le_rfl hsp
          | exact mul_le_mul_left hsp _
          | (rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
             exact Submodule.mul_le_mul_right (FractionalIdeal.coe_le_coe.mpr hsp))
      _ = 1 := inv_mul_cancel₀ hb
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hc1
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hs0
    rw [← hbc, ← hI]
    simp
  have key : FractionalIdeal.absNorm b * FractionalIdeal.absNorm
      (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) = |Algebra.norm ℚ l| := by
    rw [← map_mul, hbc, FractionalIdeal.absNorm_span_singleton]
  have hx : (1 : ℚ) ≤ FractionalIdeal.absNorm
      (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) := by
    rw [← hI, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I ≠ 0 := fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.mp h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have ha : (0 : ℚ) ≤ FractionalIdeal.absNorm b := FractionalIdeal.absNorm_nonneg b
  have hq : (FractionalIdeal.absNorm b : ℚ) ≤ |Algebra.norm ℚ l| := by
    calc (FractionalIdeal.absNorm b : ℚ) = FractionalIdeal.absNorm b * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hx ha
      _ = _ := key
  exact_mod_cast hq

end Norm

end Formalism.FourierDecayAlt.P.W

namespace Formalism.FourierDecayAlt.P

open NumberField

theorem word_fusion : Formalism.FourierDecayAlt.W.WordFusion := by
  unfold Formalism.FourierDecayAlt.W.WordFusion
  intro R B _ _ _ L h hp
  exact Formalism.FourierDecayAlt.P.W.wordFusion_list L h hp

theorem norm_lower_bound : Formalism.FourierDecayAlt.W.NormLower := by
  unfold Formalism.FourierDecayAlt.W.NormLower
  intro E _ _ _ aa l hl hl0
  have hb : aa ≠ 0 := by
    rintro rfl
    first
    | exact hl0 ((FractionalIdeal.mem_zero_iff _).mp hl)
    | exact hl0 (FractionalIdeal.mem_zero_iff.mp hl)
    | (simp at hl; exact hl0 hl)
  have h1 := Formalism.FourierDecayAlt.P.W.absNorm_le_norm aa hb l hl hl0
  have hsq : (∏ w : NumberField.InfinitePlace E, w l) ^ 2 =
      ∏ w : NumberField.InfinitePlace E, w l ^ w.mult := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    have hc : ¬ w.IsReal :=
      NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex w)
    first
    | rw [NumberField.InfinitePlace.mult, if_neg hc]
    | simp [NumberField.InfinitePlace.mult, hc]
  have hprod : (∏ w : NumberField.InfinitePlace E, w l) ^ 2 = |(Algebra.norm ℚ l : ℝ)| := by
    rw [hsq, NumberField.InfinitePlace.prod_eq_abs_norm]
    first
    | rfl
    | simp
    | (push_cast; rfl)
  have hnn : 0 ≤ ∏ w : NumberField.InfinitePlace E, w l := by
    refine Finset.prod_nonneg (fun w _ => ?_)
    first
    | positivity
    | exact w.nonneg l
    | exact AbsoluteValue.nonneg _ _
  rw [← Real.sqrt_sq hnn, hprod]
  exact Real.sqrt_le_sqrt h1

end Formalism.FourierDecayAlt.P
