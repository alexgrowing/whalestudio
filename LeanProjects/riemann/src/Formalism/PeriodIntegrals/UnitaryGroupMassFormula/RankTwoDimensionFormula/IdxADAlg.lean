import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame

noncomputable section

open Matrix

namespace PI.UnitaryDimensionFormula

section DAlg

variable {A : Type} [CommRing A] (σ : A →+* A) {n k : ℕ} (J : Matrix (Fin n) (Fin n) A)

def daB (x : Fin k → Fin n → A) : Matrix (Fin n) (Fin k) A := Matrix.of fun p i => x i p

def daP (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) : Matrix (Fin n) (Fin n) A :=
  daB x * M * (Formalism.UG.cT σ (daB y) * J)

def daT (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) : Matrix (Fin n) (Fin n) A :=
  J * daB x * M * (Formalism.UG.cT σ (daB y) * J)

theorem da_gram (x y : Fin k → Fin n → A) (i j : Fin k) :
    (Formalism.UG.cT σ (daB x) * J * daB y) i j = Formalism.UG.hform σ J (x i) (y j) := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.hform, daB, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem da_mulVec (y : Fin k → Fin n → A) (v : Fin n → A) (i : Fin k) :
    ((Formalism.UG.cT σ (daB y) * J) *ᵥ v) i = Formalism.UG.hform σ J (y i) v := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.hform, daB, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem da_row (y : Fin k → Fin n → A) (j : Fin k) (q : Fin n) :
    (Formalism.UG.cT σ (daB y) * J) j q = hrow σ J (y j) q := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, hrow, daB, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]

theorem da_sum (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) :
    ∑ i, ∑ j, M i j • Matrix.vecMulVec (x i) (hrow σ J (y j)) = daP σ J x y M := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, daP, Matrix.mul_apply,
    da_row, daB, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [hrow, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    ring

theorem da_sMat (b bs : Fin k → Fin n → A) (C D : Matrix (Fin k) (Fin k) A) :
    sMat σ J b bs C D = 1 + daP σ J b bs (C - 1) + daP σ J bs b (D - 1) := by
  unfold sMat
  simp only [Finset.sum_add_distrib, da_sum, add_assoc]

variable {σ}

theorem da_cT_cT (hσ : ∀ a, σ (σ a) = a) {m p : Type} (M : Matrix m p A) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j
  simp [Formalism.UG.cT, hσ]

theorem da_cT_add {m p : Type} (M N : Matrix m p A) :
    Formalism.UG.cT σ (M + N) = Formalism.UG.cT σ M + Formalism.UG.cT σ N := by
  ext i j
  simp [Formalism.UG.cT]

theorem da_cT_sub {m p : Type} (M N : Matrix m p A) :
    Formalism.UG.cT σ (M - N) = Formalism.UG.cT σ M - Formalism.UG.cT σ N := by
  ext i j
  simp [Formalism.UG.cT]

theorem da_herm (hσ : ∀ a, σ (σ a) = a) (hJ : Formalism.UG.IsHerm σ J) (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = σ (Formalism.UG.hform σ J y x) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have h := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using h
  simp only [Formalism.UG.hform, map_sum, map_mul, hσ, hJ']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smul_l (c : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smul_r (c : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem da_smulB (c : A) (x : Fin k → Fin n → A) (hx : ∀ i, x i = c • x i) : c • daB x = daB x := by
  ext p i
  simp only [daB, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact (congrFun (hx i) p).symm

theorem da_PP (x y : Fin k → Fin n → A) (c : A) (hm : Formalism.UG.cT σ (daB y) * J * daB x = c • 1)
    (hx : c • daB x = daB x) (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y M * daP σ J x y N = daP σ J x y (M * N) := by
  unfold daP
  calc daB x * M * (Formalism.UG.cT σ (daB y) * J) * (daB x * N * (Formalism.UG.cT σ (daB y) * J))
        = daB x * M * (Formalism.UG.cT σ (daB y) * J * daB x) * N * (Formalism.UG.cT σ (daB y) * J) := by
          simp only [Matrix.mul_assoc]
    _ = (c • daB x) * (M * N) * (Formalism.UG.cT σ (daB y) * J) := by
          rw [hm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = daB x * (M * N) * (Formalism.UG.cT σ (daB y) * J) := by rw [hx]

theorem parabolic_product_zero (x y x' y' : Fin k → Fin n → A) (hm : Formalism.UG.cT σ (daB y) * J * daB x' = 0)
    (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y M * daP σ J x' y' N = 0 := by
  unfold daP
  calc daB x * M * (Formalism.UG.cT σ (daB y) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = daB x * M * (Formalism.UG.cT σ (daB y) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hm]; simp

theorem da_P_add (x y : Fin k → Fin n → A) (M N : Matrix (Fin k) (Fin k) A) :
    daP σ J x y (M + N) = daP σ J x y M + daP σ J x y N := by
  unfold daP
  simp only [Matrix.mul_add, Matrix.add_mul]

private theorem cT_mul_lemma {m p q : Type} [Fintype p] (X : Matrix m p A) (Y : Matrix p q A) :
    Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem da_cTP (hσ : ∀ a, σ (σ a) = a) (hJ : Formalism.UG.IsHerm σ J) (x y : Fin k → Fin n → A)
    (M : Matrix (Fin k) (Fin k) A) :
    Formalism.UG.cT σ (daP σ J x y M) * J = daT σ J y x (Formalism.UG.cT σ M) := by
  unfold daP daT
  simp only [cT_mul_lemma]
  rw [da_cT_cT hσ, show Formalism.UG.cT σ J = J from hJ]
  simp only [Matrix.mul_assoc]

theorem da_JP (x y : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A) :
    J * daP σ J x y M = daT σ J x y M := by
  unfold daP daT
  simp only [Matrix.mul_assoc]

theorem da_TRI (hσ : ∀ a, σ (σ a) = a) (hJ : Formalism.UG.IsHerm σ J) (x y x' y' : Fin k → Fin n → A) (c : A)
    (hm : Formalism.UG.cT σ (daB x) * J * daB x' = c • 1) (hy : c • daB y = daB y) (M N : Matrix (Fin k) (Fin k) A) :
    Formalism.UG.cT σ (daP σ J x y M) * J * daP σ J x' y' N = daT σ J y y' (Formalism.UG.cT σ M * N) := by
  rw [da_cTP J hσ hJ]
  unfold daT daP
  calc J * daB y * Formalism.UG.cT σ M * (Formalism.UG.cT σ (daB x) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = J * daB y * Formalism.UG.cT σ M * (Formalism.UG.cT σ (daB x) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = J * (c • daB y) * (Formalism.UG.cT σ M * N) * (Formalism.UG.cT σ (daB y') * J) := by
          rw [hm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = J * daB y * (Formalism.UG.cT σ M * N) * (Formalism.UG.cT σ (daB y') * J) := by rw [hy]

theorem transfer_triple_zero (hσ : ∀ a, σ (σ a) = a) (hJ : Formalism.UG.IsHerm σ J) (x y x' y' : Fin k → Fin n → A)
    (hm : Formalism.UG.cT σ (daB x) * J * daB x' = 0) (M N : Matrix (Fin k) (Fin k) A) :
    Formalism.UG.cT σ (daP σ J x y M) * J * daP σ J x' y' N = 0 := by
  rw [da_cTP J hσ hJ]
  unfold daT daP
  calc J * daB y * Formalism.UG.cT σ M * (Formalism.UG.cT σ (daB x) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = J * daB y * Formalism.UG.cT σ M * (Formalism.UG.cT σ (daB x) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hm]; simp

theorem da_TP (x y x' y' : Fin k → Fin n → A) (c : A)
    (hm : Formalism.UG.cT σ (daB x) * J * daB x' = c • 1) (hy : c • daB y = daB y) (M N : Matrix (Fin k) (Fin k) A) :
    daT σ J y x M * daP σ J x' y' N = daT σ J y y' (M * N) := by
  unfold daT daP
  calc J * daB y * M * (Formalism.UG.cT σ (daB x) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = J * daB y * M * (Formalism.UG.cT σ (daB x) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = J * (c • daB y) * (M * N) * (Formalism.UG.cT σ (daB y') * J) := by
          rw [hm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = J * daB y * (M * N) * (Formalism.UG.cT σ (daB y') * J) := by rw [hy]

theorem transfer_product_zero (x y x' y' : Fin k → Fin n → A)
    (hm : Formalism.UG.cT σ (daB x) * J * daB x' = 0) (M N : Matrix (Fin k) (Fin k) A) :
    daT σ J y x M * daP σ J x' y' N = 0 := by
  unfold daT daP
  calc J * daB y * M * (Formalism.UG.cT σ (daB x) * J) * (daB x' * N * (Formalism.UG.cT σ (daB y') * J))
        = J * daB y * M * (Formalism.UG.cT σ (daB x) * J * daB x') * N * (Formalism.UG.cT σ (daB y') * J) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hm]; simp

end DAlg

theorem idxDAlg : IdxDAlg := by
  intro A _ σ n k J ε b bs hσ hJ hfr
  obtain ⟨hεε, hεσ, hb, hbs, hbb⟩ := hfr
  have hx1 : ε • daB b = daB b := da_smulB ε b hb
  have hx2 : σ ε • daB bs = daB bs := da_smulB (σ ε) bs hbs
  have hm1 : Formalism.UG.cT σ (daB bs) * J * daB b = ε • (1 : Matrix (Fin k) (Fin k) A) := by
    ext i j
    rw [da_gram, hbb i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hm2 : Formalism.UG.cT σ (daB b) * J * daB bs = σ ε • (1 : Matrix (Fin k) (Fin k) A) := by
    ext i j
    rw [da_gram, da_herm J hσ hJ, hbb j i, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  have hm3 : Formalism.UG.cT σ (daB bs) * J * daB bs = 0 := by
    ext i j
    rw [da_gram, Matrix.zero_apply, hbs i, hbs j, da_smul_l, da_smul_r, hσ, ← mul_assoc, hεσ, zero_mul]
  have hm4 : Formalism.UG.cT σ (daB b) * J * daB b = 0 := by
    ext i j
    rw [da_gram, Matrix.zero_apply, hb i, hb j, da_smul_l, da_smul_r, ← mul_assoc, mul_comm (σ ε) ε, hεσ,
      zero_mul]
  have hPP : ∀ M N, daP σ J b bs M * daP σ J b bs N = daP σ J b bs (M * N) :=
    fun M N => da_PP J b bs ε hm1 hx1 M N
  have hQQ : ∀ M N, daP σ J bs b M * daP σ J bs b N = daP σ J bs b (M * N) :=
    fun M N => da_PP J bs b (σ ε) hm2 hx2 M N
  have hPQ : ∀ M N, daP σ J b bs M * daP σ J bs b N = 0 := fun M N => parabolic_product_zero J b bs bs b hm3 M N
  have hQP : ∀ M N, daP σ J bs b M * daP σ J b bs N = 0 := fun M N => parabolic_product_zero J bs b b bs hm4 M N
  have hc1 : Formalism.UG.cT σ (1 : Matrix (Fin k) (Fin k) A) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hc1n : Formalism.UG.cT σ (1 : Matrix (Fin n) (Fin n) A) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hTadd : ∀ (x y : Fin k → Fin n → A) (M N : Matrix (Fin k) (Fin k) A),
      daT σ J x y (M + N) = daT σ J x y M + daT σ J x y N := by
    intro x y M N
    unfold daT
    simp only [Matrix.mul_add, Matrix.add_mul]
  have hT0 : ∀ x y : Fin k → Fin n → A, daT σ J x y 0 = 0 := by
    intro x y
    unfold daT
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C D y hy
    have h0 : ∀ (x y' : Fin k → Fin n → A) (M : Matrix (Fin k) (Fin k) A),
        (∀ j, Formalism.UG.hform σ J (y' j) y = 0) → daP σ J x y' M *ᵥ y = 0 := by
      intro x y' M hz
      unfold daP
      rw [← Matrix.mulVec_mulVec]
      have hz' : (Formalism.UG.cT σ (daB y') * J) *ᵥ y = 0 := by
        ext i
        rw [da_mulVec]
        exact hz i
      rw [hz', Matrix.mulVec_zero]
    rw [da_sMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      h0 b bs _ (fun j => (hy j).2), h0 bs b _ (fun j => (hy j).1), add_zero, add_zero]
  · intro C₁ D₁ C₂ D₂
    rw [da_sMat, da_sMat, da_sMat]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hPP, hQQ, hPQ, hQP,
      add_zero]
    rw [show C₁ * C₂ - 1 = (C₁ - 1) + (C₂ - 1) + (C₁ - 1) * (C₂ - 1) by noncomm_ring,
      show D₁ * D₂ - 1 = (D₁ - 1) + (D₂ - 1) + (D₁ - 1) * (D₂ - 1) by noncomm_ring,
      da_P_add, da_P_add, da_P_add, da_P_add]
    abel
  · intro C D hC hD
    have hP : daP σ J b bs (C - 1) = 0 := by
      unfold daP
      rw [← hx1, Matrix.smul_mul, ← Matrix.mul_smul, hC]
      simp
    have hQ : daP σ J bs b (D - 1) = 0 := by
      unfold daP
      rw [← hx2, Matrix.smul_mul, ← Matrix.mul_smul, hD]
      simp
    rw [da_sMat, hP, hQ, add_zero, add_zero]
  · intro C C' hCC
    have hDt : (C'.map σ)ᵀ = Formalism.UG.cT σ C' := rfl
    rw [hDt, da_sMat]
    have hZ1 : (C - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) * (C - 1) = 0 := by
      rw [da_cT_sub, da_cT_cT hσ, hc1,
        show C - 1 + (C' - 1) + (C' - 1) * (C - 1) = C' * C - 1 by noncomm_ring, hCC, sub_self]
    have hZ2 : (Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (C - 1) + Formalism.UG.cT σ (C - 1) * (Formalism.UG.cT σ C' - 1) = 0 := by
      rw [da_cT_sub, hc1,
        show Formalism.UG.cT σ C' - 1 + (Formalism.UG.cT σ C - 1) + (Formalism.UG.cT σ C - 1) * (Formalism.UG.cT σ C' - 1) =
          Formalism.UG.cT σ C * Formalism.UG.cT σ C' - 1 by noncomm_ring,
        ← cT_mul_lemma, hCC, hc1, sub_self]
    calc Formalism.UG.cT σ (1 + daP σ J b bs (C - 1) + daP σ J bs b (Formalism.UG.cT σ C' - 1)) * J *
          (1 + daP σ J b bs (C - 1) + daP σ J bs b (Formalism.UG.cT σ C' - 1))
        = J + daT σ J b bs ((C - 1) + Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) +
              Formalism.UG.cT σ (Formalism.UG.cT σ C' - 1) * (C - 1)) +
            daT σ J bs b ((Formalism.UG.cT σ C' - 1) + Formalism.UG.cT σ (C - 1) +
              Formalism.UG.cT σ (C - 1) * (Formalism.UG.cT σ C' - 1)) := by
          rw [da_cT_add, da_cT_add, hc1n]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, da_cTP J hσ hJ, da_JP,
            da_TP J b bs bs b (σ ε) hm2 hx2, da_TP J bs b b bs ε hm1 hx1, transfer_product_zero J b bs b bs hm4,
            transfer_product_zero J bs b bs b hm3, add_zero, hTadd]
          abel
      _ = J := by rw [hZ1, hZ2, hT0, hT0, add_zero, add_zero]

end PI.UnitaryDimensionFormula
