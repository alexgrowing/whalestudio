import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame

noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.InertThetaCompare

namespace GlobalTheory.LFun.CellBound

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

private theorem det_mem_foundation {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m L)
    (h : ∀ i j, M i j ∈ intL L) : M.det ∈ intL L := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

private theorem valuation_zpow_uniformizer' {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem valuation_prod_zpow_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {ι : Type}
    (s : Finset ι) (m : ι → ℤ) :
    Valued.v (∏ i ∈ s, ϖ ^ m i) = WithZero.exp (-∑ i ∈ s, m i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro j s hj ih
    rw [Finset.prod_insert hj, Finset.sum_insert hj, map_mul, ih, valuation_zpow_uniformizer' hϖ, ← WithZero.exp_add]
    congr 1
    ring

theorem minor_le {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {a μ : Fin n → ℤ}
    {b k₁ k₂ : Matrix (Fin n) (Fin n) L} (hb : b.BlockTriangular id) (hd : ∀ i, b i i = ϖ ^ a i)
    (h₁ : ∀ i j, k₁ i j ∈ intL L) (h₂ : ∀ i j, k₂ i j ∈ intL L)
    (e : b = k₁ * Matrix.diagonal (fun i => ϖ ^ μ i) * k₂) (I : Finset (Fin n)) (c : ℤ)
    (hc : ∀ S : Finset (Fin n), S.card = I.card → c ≤ ∑ i ∈ S, μ i) :
    c ≤ ∑ i ∈ I, a i := by
  classical
  have hint : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  let A : Matrix I (Fin n) L := fun i s => k₁ i s * ϖ ^ μ s
  let B : Matrix (Fin n) I L := fun s j => k₂ s j
  have hM : b.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n)) = A * B := by
    ext i j
    rw [Matrix.mul_apply]
    simp [A, B, e, Matrix.mul_apply, Matrix.diagonal_apply]
  have hdet : (b.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).det =
      ∏ i : I, ϖ ^ a i := by
    have ht : (b.submatrix (fun i : I => (i : Fin n)) (fun i : I => (i : Fin n))).BlockTriangular id :=
      fun i j hij => hb (show (j : Fin n) < i from hij)
    rw [Matrix.det_of_upperTriangular ht]
    simp [hd]
  have hexp : (A * B).det = ∑ f : I → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    simp only [Matrix.det_apply, Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
      Finset.smul_sum, Finset.mul_sum, Matrix.submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]
    ring
  have hterm : ∀ f : I → Fin n,
      Valued.v ((∏ i, B (f i) i) * (A.submatrix id f).det) ≤ WithZero.exp (-c) := by
    intro f
    by_cases hf : Function.Injective f
    · have hA : A.submatrix id f = k₁.submatrix (fun i : I => (i : Fin n)) f *
          Matrix.diagonal (fun j => ϖ ^ μ (f j)) := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, id]
        rfl
      rw [hA, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_mul, valuation_prod_zpow_uniformizer hϖ]
      have h1 : Valued.v (∏ i, B (f i) i) ≤ 1 := (hint _).mp (prod_mem fun i _ => h₂ _ _)
      have h2 : Valued.v (k₁.submatrix (fun i : I => (i : Fin n)) f).det ≤ 1 :=
        (hint _).mp (det_mem_foundation _ fun i j => h₁ _ _)
      have h3 : c ≤ ∑ i, μ (f i) := by
        have := hc (Finset.univ.image f)
          (by rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe])
        rwa [Finset.sum_image (fun x _ y _ h => hf h)] at this
      calc Valued.v (∏ i, B (f i) i) *
            (Valued.v (k₁.submatrix (fun i : I => (i : Fin n)) f).det * WithZero.exp (-∑ i, μ (f i)))
          ≤ 1 * (1 * WithZero.exp (-∑ i, μ (f i))) := mul_le_mul' h1 (mul_le_mul' h2 le_rfl)
        _ ≤ WithZero.exp (-c) := by rw [one_mul, one_mul, WithZero.exp_le_exp]; omega
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        simp only [Function.Injective, not_forall] at hf
        obtain ⟨i, j, h, hne⟩ := hf
        exact ⟨i, j, h, hne⟩
      rw [Matrix.det_zero_of_column_eq hne (fun r => by simp [hij]), mul_zero, map_zero]
      exact zero_le'
  have hle : Valued.v (∏ i : I, ϖ ^ a i) ≤ WithZero.exp (-c) := by
    rw [← hdet, hM, hexp]
    exact Valuation.map_sum_le _ fun f _ => hterm f
  rw [valuation_prod_zpow_uniformizer hϖ, WithZero.exp_le_exp] at hle
  have : ∑ i : I, a i = ∑ i ∈ I, a i := Finset.sum_coe_sort I a
  omega

end Local

theorem tExp_lo {n : ℕ} (a : Fin (n / 2) → ℤ) (i : Fin (n / 2)) :
    tExp n (n / 2) a ⟨i.1, by omega⟩ = a i := by
  unfold tExp
  split_ifs with h h'
  · rfl
  · exact absurd i.2 h
  · exact absurd i.2 h

theorem tExp_hi {n : ℕ} (a : Fin (n / 2) → ℤ) (i : Fin (n / 2)) :
    tExp n (n / 2) a ⟨n - 1 - i.1, by omega⟩ = -a i := by
  have hi := i.2
  have e : n - 1 - (n - 1 - i.1) = i.1 := by omega
  unfold tExp
  split_ifs with h h'
  · exfalso
    have h2 : n - 1 - i.1 < n / 2 := h
    omega
  · rw [neg_inj]
    congr 1
    apply Fin.ext
    exact e
  · exfalso
    exact h' ⟨by show n - n / 2 ≤ n - 1 - i.1; omega, by show n - 1 - (n - 1 - i.1) < n / 2; omega⟩

theorem sum_min_tExp {n : ℕ} (a : Fin (n / 2) → ℤ) :
    ∑ j, min (tExp n (n / 2) a j) 0 = -∑ i, |a i| := by
  set f : Fin n → ℤ := fun j => min (tExp n (n / 2) a j) 0 with hf
  let lo : Fin (n / 2) → Fin n := fun i => ⟨i.1, by omega⟩
  let hi : Fin (n / 2) → Fin n := fun i => ⟨n - 1 - i.1, by omega⟩
  have hlo : Function.Injective lo := fun i i' h => Fin.ext (by simpa [lo] using congrArg Fin.val h)
  have hhi : Function.Injective hi := by
    intro i i' h
    have := congrArg Fin.val h
    simp only [hi] at this
    have := i.2; have := i'.2
    exact Fin.ext (by omega)
  have hdisj : Disjoint (Finset.univ.image lo) (Finset.univ.image hi) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨i', -, h⟩ := Finset.mem_image.mp hj'
    have := congrArg Fin.val h
    simp only [lo, hi] at this
    have := i.2; have := i'.2
    omega
  have hzero : ∀ j ∉ Finset.univ.image lo ∪ Finset.univ.image hi, f j = 0 := by
    intro j hj
    rw [Finset.mem_union, not_or] at hj
    simp only [hf]
    unfold tExp
    split_ifs with h1 h2
    · exact (hj.1 (Finset.mem_image.mpr ⟨⟨j.1, h1⟩, Finset.mem_univ _, rfl⟩)).elim
    · exfalso
      apply hj.2
      refine Finset.mem_image.mpr ⟨⟨n - 1 - j.1, h2.2⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext (by show n - 1 - (n - 1 - j.1) = j.1; have := j.2; omega)
    · simp
  rw [← Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hzero j hj),
    Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => hlo h),
    Finset.sum_image (fun x _ y _ h => hhi h), ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hf, lo, hi, tExp_lo, tExp_hi]
  rcases le_total (a i) 0 with h | h
  · rw [abs_of_nonpos h, min_eq_left h, min_eq_right (by omega)]; ring
  · rw [abs_of_nonneg h, min_eq_right h, min_eq_left (by omega)]; ring

theorem neg_one_le_tExp {n : ℕ} {a : Fin (n / 2) → ℤ} (h : ∀ i, |a i| ≤ 1) (j : Fin n) :
    -1 ≤ tExp n (n / 2) a j := by
  unfold tExp
  split_ifs with h1 h2
  · exact (abs_le.mp (h _)).1
  · have := (abs_le.mp (h ⟨n - 1 - j.1, h2.2⟩)).2
    omega
  · norm_num

private theorem entries_mem_intL_of_mem_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    {σ : L →+* L} {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) (i j : Fin n) :
    ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L := by
  rw [KU, Subgroup.mem_subgroupOf] at hk
  unfold intPts at hk
  obtain ⟨g, hg⟩ := (Subgroup.mem_inf.mp hk).2
  rw [← hg]
  unfold bc
  exact ((g : Matrix (Fin n) (Fin n) (intL L)) i j).2

private theorem tMat_eq_diagonal_pow_tExp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (n : ℕ) (a : Fin (n / 2) → ℤ) :
    tMat ϖ n (n / 2) a = Matrix.diagonal (fun j => ϖ ^ tExp n (n / 2) a j) := by
  unfold tMat tExp
  congr 1
  funext j
  split_ifs <;> simp

theorem cell_bound : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (ε κ : Fin (n / 2) → ℤ) (u k k₁ k₂ : GU σ n), (∀ i, |ε i| ≤ 1) → IsUnipU u → k ∈ KU σ n → k₁ ∈ KU σ n → k₂ ∈ KU σ n → tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * tMat ϖ n (n / 2) ε * ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i| := by
  intro L _ _ ϖ σ q n hU ε κ u k k₁ k₂ hε hu hk hk₁ hk₂ e
  classical
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  set U := ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hU'
  set K := ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hK
  set K₁ := ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hK₁
  set K₂ := ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hK₂
  set Ki := (((k⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hKi
  have hKK : K * Ki = 1 := by
    show ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((k : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1
    exact Units.mul_inv _
  have hint₂ : ∀ i j, (K₂ * Ki) i j ∈ intL L := fun i j =>
    entries_mem_intL_of_mem_KU (mul_mem hk₂ (inv_mem hk)) i j
  set b := tMat ϖ n (n / 2) κ * U with hbdef
  have hbe : b = K₁ * Matrix.diagonal (fun j => ϖ ^ tExp n (n / 2) ε j) * (K₂ * Ki) := by
    calc b = b * (K * Ki) := by rw [hKK, Matrix.mul_one]
      _ = (b * K) * Ki := (Matrix.mul_assoc b K Ki).symm
      _ = K₁ * tMat ϖ n (n / 2) ε * K₂ * Ki := by rw [e]
      _ = _ := by rw [tMat_eq_diagonal_pow_tExp, Matrix.mul_assoc]
  have hbT : b.BlockTriangular id := by
    intro i j hij
    rw [hbdef, tMat_eq_diagonal_pow_tExp, Matrix.diagonal_mul]
    exact mul_eq_zero_of_right _ (show U i j = 0 from hu.1 i j hij)
  have hbd : ∀ j, b j j = ϖ ^ tExp n (n / 2) κ j := by
    intro j
    rw [hbdef, tMat_eq_diagonal_pow_tExp, Matrix.diagonal_mul, show U j j = 1 from hu.2 j, mul_one]
  have key := fun I c hc => minor_le hϖ hbT hbd (fun i j => entries_mem_intL_of_mem_KU hk₁ i j) hint₂ hbe I c hc
  have hlow : ∀ j, -1 ≤ tExp n (n / 2) κ j := by
    intro j
    have := key {j} (-1) (by
      intro S hS
      obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp (by rw [hS, Finset.card_singleton])
      rw [Finset.sum_singleton]
      exact neg_one_le_tExp hε s)
    rwa [Finset.sum_singleton] at this
  refine ⟨fun i => abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · have := hlow ⟨i.1, by omega⟩
    rwa [tExp_lo] at this
  · have := hlow ⟨n - 1 - i.1, by omega⟩
    rw [tExp_hi] at this
    linarith
  · have hS : ∀ S : Finset (Fin n), -∑ i, |ε i| ≤ ∑ i ∈ S, tExp n (n / 2) ε i := by
      intro S
      rw [← sum_min_tExp, ← Finset.sum_sdiff (Finset.subset_univ S)]
      have h1 : ∑ i ∈ Finset.univ \ S, min (tExp n (n / 2) ε i) 0 ≤ 0 :=
        Finset.sum_nonpos fun i _ => min_le_right _ _
      have h2 : ∑ i ∈ S, min (tExp n (n / 2) ε i) 0 ≤ ∑ i ∈ S, tExp n (n / 2) ε i :=
        Finset.sum_le_sum fun i _ => min_le_left _ _
      linarith
    have := key (Finset.univ.filter fun j => tExp n (n / 2) κ j < 0) _ (fun S _ => hS S)
    rw [Finset.sum_filter] at this
    have h3 : ∑ j, (if tExp n (n / 2) κ j < 0 then tExp n (n / 2) κ j else 0) =
        ∑ j, min (tExp n (n / 2) κ j) 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · exact (min_eq_left h.le).symm
      · exact (min_eq_right (not_lt.mp h)).symm
    rw [h3, sum_min_tExp] at this
    linarith

end GlobalTheory.LFun.CellBound

end
