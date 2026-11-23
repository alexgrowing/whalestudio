import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBounded
open Matrix GlobalTheory.ClassFin

namespace GlobalTheory.ReducedBasisBound

lemma abs_sum_le_card {N : ℕ} (f : Fin N → ℝ) (B : ℝ) (h : ∀ p, |f p| ≤ B) :
    |∑ p, f p| ≤ N * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p, |f p| ≤ ∑ _p : Fin N, B := Finset.sum_le_sum (fun p _ => h p)
    _ = N * B := by simp

lemma entry_eq {N : ℕ} (a : Fin N → ℝ) (n Z P : Matrix (Fin N) (Fin N) ℝ)
    (h : diagonal a * n * P = Z * diagonal a * n) (p j : Fin N) :
    a p * (n * P) p j = ∑ q, Z p q * a q * n q j := by
  have := congrFun (congrFun h p) j
  rw [Matrix.mul_assoc, diagonal_mul] at this
  rw [this, Matrix.mul_apply]
  simp [mul_diagonal]

lemma int_eq_zero {x : ℤ} (h : |(x : ℝ)| < 1) : x = 0 := by
  have : |x| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp this

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}

lemma integral_entry_eq_zero (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T)
    (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hmn : m * n = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hε : 0 < ε) (hK : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) < 1) :
    ∀ i j, a i ≤ ε * a j → M' j i = 0 := by
  intro i j hij
  apply int_eq_zero
  have hC0 : 0 ≤ C₁ := by linarith
  have hM' : M'.map (Int.cast : ℤ → ℝ) = m * (n * M'.map (Int.cast : ℤ → ℝ)) := by
    rw [← Matrix.mul_assoc, hmn, Matrix.one_mul]
  have hE : ∀ p, j ≤ p → |(n * M'.map (Int.cast : ℤ → ℝ)) p i| ≤ N * (T * C₁ ^ 3 * ε) := by
    intro p hp
    have he := entry_eq a n Zᵀ _ h2 p i
    have hb : |∑ q, Zᵀ p q * a q * n q i| ≤ N * (T * C₁ ^ 3 * ε * a p) := by
      apply abs_sum_le_card
      intro q
      rcases le_or_gt q i with hq | hq
      · have haq : a q ≤ C₁ ^ 2 * ε * a p := by
          calc a q ≤ C₁ * a i := hle q i hq
            _ ≤ C₁ * (ε * a j) := by gcongr
            _ ≤ C₁ * (ε * (C₁ * a p)) := by gcongr; exact hle j p hp
            _ = C₁ ^ 2 * ε * a p := by ring
        rw [abs_mul, abs_mul, transpose_apply, abs_of_pos (ha q)]
        calc |Z q p| * a q * |n q i| ≤ T * (C₁ ^ 2 * ε * a p) * C₁ := by
              have := ha p
              exact mul_le_mul (mul_le_mul (hZ q p) haq (ha q).le hT) (hn q i) (abs_nonneg _) (by positivity)
          _ = T * C₁ ^ 3 * ε * a p := by ring
      · rw [hn_low q i hq]
        have := ha p
        simp only [mul_zero, abs_zero]
        positivity
    have : a p * |(n * M'.map (Int.cast : ℤ → ℝ)) p i| ≤ a p * (N * (T * C₁ ^ 3 * ε)) := by
      rw [← abs_of_pos (ha p), ← abs_mul, he, abs_of_pos (ha p)]
      calc _ ≤ N * (T * C₁ ^ 3 * ε * a p) := hb
        _ = a p * (N * (T * C₁ ^ 3 * ε)) := by ring
    exact le_of_mul_le_mul_left this (ha p)
  have hentry : ((M' j i : ℤ) : ℝ) = (M'.map (Int.cast : ℤ → ℝ)) j i := by simp
  rw [hentry, hM', mul_apply]
  refine lt_of_le_of_lt (abs_sum_le_card _ _ (fun p => ?_)) hK
  rcases le_or_gt j p with hp | hp
  · rw [abs_mul]
    exact mul_le_mul (hm j p) (hE p hp) (abs_nonneg _) hCm
  · rw [hm_low j p hp, zero_mul, abs_zero]
    have : (0 : ℝ) ≤ N * (T * C₁ ^ 3 * ε) := by positivity
    positivity

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}

lemma conj_entry_eq_zero (hC : 1 ≤ C₁) (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hnm : n * m = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hA : ∀ i j, a i ≤ ε * a j → M' j i = 0) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ * C₁ ^ 2 = ε) :
    ∀ i j, a i ≤ δ * a j → Z i j = 0 := by
  intro i j hij
  have hC0 : 0 ≤ C₁ := by linarith
  have h := congrArg (· * m) h2
  simp only [Matrix.mul_assoc] at h
  rw [hnm, Matrix.mul_one] at h
  have e := congrFun (congrFun h j) i
  rw [diagonal_mul, mul_diagonal, transpose_apply] at e
  have hz : (n * (M'.map (Int.cast : ℤ → ℝ) * m)) j i = 0 := by
    rw [mul_apply]
    apply Finset.sum_eq_zero
    intro p _
    rcases lt_or_ge p j with hp | hp
    · rw [hn_low j p hp, zero_mul]
    · have hin : (M'.map (Int.cast : ℤ → ℝ) * m) p i = 0 := by
        rw [mul_apply]
        apply Finset.sum_eq_zero
        intro q _
        rcases lt_or_ge i q with hq | hq
        · rw [hm_low q i hq, mul_zero]
        · have hq' : a q ≤ ε * a p := by
            calc a q ≤ C₁ * a i := hle q i hq
              _ ≤ C₁ * (δ * a j) := by gcongr
              _ ≤ C₁ * (δ * (C₁ * a p)) := by gcongr; exact hle j p hp
              _ = ε * a p := by rw [← hδ]; ring
          rw [Matrix.map_apply, hA q p hq']
          simp
      rw [hin, mul_zero]
  rw [hz, mul_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_right (ne_of_gt (ha i))

lemma entry_bound_of_vanishing (hC : 1 ≤ C₁) (hCm : 0 ≤ Cm) (hT : 0 ≤ T) (ha : ∀ i, 0 < a i)
    (hmn : m * n = 1) (hn : ∀ i j, |n i j| ≤ C₁) (hm : ∀ i j, |m i j| ≤ Cm) (hZ : ∀ i j, |Z i j| ≤ T)
    (M : Matrix (Fin N) (Fin N) ℤ)
    (h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n)
    (δ : ℝ) (hδ : 0 < δ) (hB : ∀ i j, a i ≤ δ * a j → Z i j = 0) :
    ∀ i j, |(M i j : ℝ)| ≤ N * (Cm * (N * (T * C₁ / δ))) := by
  intro i j
  have hC0 : 0 ≤ C₁ := by linarith
  have hM : M.map (Int.cast : ℤ → ℝ) = m * (n * M.map (Int.cast : ℤ → ℝ)) := by
    rw [← Matrix.mul_assoc, hmn, Matrix.one_mul]
  have hE : ∀ p, |(n * M.map (Int.cast : ℤ → ℝ)) p j| ≤ N * (T * C₁ / δ) := by
    intro p
    have he := entry_eq a n Z _ h1 p j
    have hb : |∑ q, Z p q * a q * n q j| ≤ N * (T * C₁ / δ * a p) := by
      apply abs_sum_le_card
      intro q
      have := ha p
      by_cases hz : Z p q = 0
      · rw [hz]
        simp only [zero_mul, abs_zero]
        positivity
      · have hlt : δ * a q < a p := by
          by_contra hc
          exact hz (hB p q (not_lt.mp hc))
        have haq : a q ≤ a p / δ := by rw [le_div_iff₀ hδ]; linarith
        rw [abs_mul, abs_mul, abs_of_pos (ha q)]
        calc _ ≤ T * (a p / δ) * C₁ :=
              mul_le_mul (mul_le_mul (hZ p q) haq (ha q).le hT) (hn q j) (abs_nonneg _) (by positivity)
          _ = T * C₁ / δ * a p := by ring
    have : a p * |(n * M.map (Int.cast : ℤ → ℝ)) p j| ≤ a p * (N * (T * C₁ / δ)) := by
      rw [← abs_of_pos (ha p), ← abs_mul, he, abs_of_pos (ha p)]
      calc _ ≤ N * (T * C₁ / δ * a p) := hb
        _ = a p * (N * (T * C₁ / δ)) := by ring
    exact le_of_mul_le_mul_left this (ha p)
  have hentry : ((M i j : ℤ) : ℝ) = (M.map (Int.cast : ℤ → ℝ)) i j := by simp
  rw [hentry, hM, mul_apply]
  exact abs_sum_le_card _ _ (fun p => by
    rw [abs_mul]; exact mul_le_mul (hm i p) (hE p) (abs_nonneg _) hCm)

end GlobalTheory.ReducedBasisBound

namespace GlobalTheory.ReducedBasisBound

lemma abs_entry_le_one {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (h : kᵀ * k = 1) (l i : Fin N) :
    |k l i| ≤ 1 := by
  have e := congrFun (congrFun h i) i
  rw [mul_apply, one_apply_eq] at e
  simp only [transpose_apply] at e
  have : k l i ^ 2 ≤ 1 := by
    rw [← e, sq]
    exact Finset.single_le_sum (f := fun l => k l i * k l i) (fun l _ => mul_self_nonneg _)
      (Finset.mem_univ l)
  exact sq_le_one_iff_abs_le_one _ |>.mp this

lemma conj_bound {N : ℕ} (k X : Matrix (Fin N) (Fin N) ℝ) (hk : ∀ l i, |k l i| ≤ 1) (R : ℝ)
    (hR : 0 ≤ R) (hX : ∀ i j, |X i j| ≤ R) (i j : Fin N) :
    |(kᵀ * X * k) i j| ≤ N * (N * R) := by
  rw [mul_apply]
  apply abs_sum_le_card
  intro q
  rw [abs_mul]
  have hin : |(kᵀ * X) i q| ≤ N * R := by
    rw [mul_apply]
    apply abs_sum_le_card
    intro l
    rw [abs_mul, transpose_apply]
    calc |k l i| * |X l q| ≤ 1 * R := mul_le_mul (hk l i) (hX l q) (abs_nonneg _) zero_le_one
      _ = R := one_mul R
  calc |(kᵀ * X) i q| * |k q j| ≤ (N * R) * 1 := mul_le_mul hin (hk q j) (abs_nonneg _) (by positivity)
    _ = N * R := mul_one _

theorem integral_conj_bounded : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ)
    (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n →
    ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) →
    (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) →
    (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) →
    ∀ i j, |(M i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨C₁, hC₁d⟩ : ∃ C₁ : ℝ, C₁ = max C 1 := ⟨_, rfl⟩
  obtain ⟨Cm0, hCm0⟩ := GlobalTheory.unipotent_upper_inv_bounded N C₁
  obtain ⟨Cm, hCmd⟩ : ∃ Cm : ℝ, Cm = max Cm0 0 := ⟨_, rfl⟩
  obtain ⟨T, hTd⟩ : ∃ T : ℝ, T = N * (N * max R 0) := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = N * (Cm * (N * (T * C₁ ^ 3))) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = 1 / (K + 1) := ⟨_, rfl⟩
  obtain ⟨δ, hδd⟩ : ∃ δ : ℝ, δ = ε / C₁ ^ 2 := ⟨_, rfl⟩
  refine ⟨N * (Cm * (N * (T * C₁ / δ))), ?_⟩
  intro k a n hs X M M' hX hM hM'
  have hC : 1 ≤ C₁ := hC₁d ▸ le_max_right _ _
  have hC₁pos : 0 < C₁ := by linarith
  have hCm : 0 ≤ Cm := hCmd ▸ le_max_right _ _
  have hR : 0 ≤ max R 0 := le_max_right _ _
  have hT : 0 ≤ T := by rw [hTd]; positivity
  have hK0 : 0 ≤ K := by rw [hKd]; positivity
  have hε : 0 < ε := by rw [hεd]; positivity
  have hKε : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) < 1 := by
    have e : (N : ℝ) * (Cm * (N * (T * C₁ ^ 3 * ε))) = K * (1 / (K + 1)) := by
      rw [← hεd, hKd]; ring
    rw [e, mul_one_div, div_lt_one (by linarith)]
    linarith
  have hδ : 0 < δ := by rw [hδd]; positivity
  have hδε : δ * C₁ ^ 2 = ε := by rw [hδd]; field_simp
  have hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact (hs.le i j h).trans
        (mul_le_mul_of_nonneg_right (hC₁d ▸ le_max_left _ _) (hs.pos j).le)
    · subst h
      nlinarith [hs.pos i]
  have hn : ∀ i j, |n i j| ≤ C₁ := fun i j => (hs.bdd i j).trans (hC₁d ▸ le_max_left _ _)
  obtain ⟨m, hmn, hnm, hm_low, hm⟩ := hCm0 n hs.diag hs.lower hn
  have hm' : ∀ i j, |m i j| ≤ Cm := fun i j => (hm i j).trans (hCmd ▸ le_max_left _ _)
  have hk := abs_entry_le_one k hs.orth
  obtain ⟨Z, hZd⟩ : ∃ Z : Matrix (Fin N) (Fin N) ℝ, Z = kᵀ * X * k := ⟨_, rfl⟩
  have hZ : ∀ i j, |Z i j| ≤ T := by
    intro i j
    rw [hZd, hTd]
    exact conj_bound k X hk _ hR (fun i j => (hX i j).trans (le_max_left _ _)) i j
  have h1 : diagonal a * n * M.map (Int.cast : ℤ → ℝ) = Z * diagonal a * n := by
    have := congrArg (kᵀ * ·) hM
    simp only [← Matrix.mul_assoc] at this
    rw [hs.orth, Matrix.one_mul] at this
    rw [this, hZd]
  have h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n := by
    have := congrArg (kᵀ * ·) hM'
    simp only [← Matrix.mul_assoc] at this
    rw [hs.orth, Matrix.one_mul] at this
    rw [this, hZd]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hA := integral_entry_eq_zero hC hCm hT hs.pos hle hmn hs.lower hm_low hn hm' hZ M' h2 ε hε hKε
  have hB := conj_entry_eq_zero hC hs.pos hle hnm hs.lower hm_low M' h2 ε hA δ hδ.le hδε
  exact entry_bound_of_vanishing hC hCm hT hs.pos hmn hn hm' hZ M h1 δ hδ hB

end GlobalTheory.ReducedBasisBound
