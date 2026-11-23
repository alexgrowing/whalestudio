import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB

open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem fSatake_borel_of_diag {d : GU σ n} {e : Fin n → L} (hd : ⟪d⟫ = Matrix.diagonal e) :
    IsBorelU d := by
  intro i j hij
  change ⟪d⟫ i j = 0
  rw [hd, Matrix.diagonal_apply_ne _ (ne_of_lt hij).symm]

theorem fSatake_borel_one : IsBorelU (1 : GU σ n) := by
  exact fSatake_borel_of_diag (e := fun _ => 1) (by rw [Matrix.diagonal_one]; simp)

theorem fSatake_ne_zero_of_borel {b : GU σ n} (hb : IsBorelU b) (i : Fin n) : ⟪b⟫ i i ≠ 0 := by
  intro h
  have hdet : (⟪b⟫).det = ∏ i, ⟪b⟫ i i :=
    Matrix.det_of_upperTriangular (fun i j hij => hb i j hij)
  have hu : IsUnit (⟪b⟫).det := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  exact hu.ne_zero (by rw [hdet]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)

theorem fSatake_tMat_apply_lt (ϖ : L) {m : ℕ} (a : Fin m → ℤ) (j : Fin m) (hj : (j : ℕ) < n) :
    tMat ϖ n m a ⟨j, hj⟩ ⟨j, hj⟩ = ϖ ^ (a j) := by
  simp [tMat, j.isLt]

theorem fSatake_borel_tMat {ϖ : L} {m : ℕ} {a : Fin m → ℤ} {t : GU σ n} (ht : ⟪t⟫ = tMat ϖ n m a) :
    IsBorelU t := by
  rw [tMat] at ht
  exact fSatake_borel_of_diag ht

theorem fSatake_tMat_exists {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    (a : Fin m → ℤ) : ∃ t : GU σ n, ⟪t⟫ = tMat ϖ n m a := by
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  have hσ : σ ϖ = ϖ := by
    obtain ⟨-, -, h, -⟩ := hU
    exact h
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have key : ∀ i j : Fin n, (i : ℕ) + j + 1 = n → tMat ϖ n m a i i * tMat ϖ n m a j j = 1 := by
    intro i j hij
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> first
      | omega
      | (simp; done)
      | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [add_neg_eq_zero]; congr 1;
          simp only [Fin.mk.injEq]; omega)
      | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [neg_add_eq_zero]; congr 1;
          simp only [Fin.mk.injEq]; omega)
  have hne : ∀ i, tMat ϖ n m a i i ≠ 0 := fun i h => by
    have hi := i.isLt
    have h2 := key i ⟨n - 1 - i, by omega⟩ (by show (i : ℕ) + (n - 1 - (i : ℕ)) + 1 = n; omega)
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hσd : ∀ i, σ (tMat ϖ n m a i i) = tMat ϖ n m a i i := by
    intro i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> simp [map_zpow₀, hσ]
  have hdiag : tMat ϖ n m a = Matrix.diagonal (fun i => tMat ϖ n m a i i) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.diagonal_apply_ne _ h, tMat, Matrix.diagonal_apply_ne _ h]
  have hinv1 : tMat ϖ n m a * Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹) = 1 := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact mul_inv_cancel₀ (hne i)
    · rw [if_neg h, tMat, Matrix.diagonal_apply_ne _ h, zero_mul]
  have hinv2 : Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹) * tMat ϖ n m a = 1 := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact inv_mul_cancel₀ (hne i)
    · rw [if_neg h, tMat, Matrix.diagonal_apply_ne _ h, mul_zero]
  refine ⟨⟨⟨tMat ϖ n m a, Matrix.diagonal (fun i => (tMat ϖ n m a i i)⁻¹), hinv1, hinv2⟩, ?_⟩, rfl⟩
  show cT σ (tMat ϖ n m a) * antiJ L n * tMat ϖ n m a = antiJ L n
  rw [hdiag, cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hσd]
  rw [antiJ]
  split_ifs with h
  · rw [mul_one]
    exact key i j h
  · simp

theorem fSatake_diag_mem_K {d : GU σ n} {e : Fin n → L} (hd : ⟪d⟫ = Matrix.diagonal e)
    (hd' : ⟪d⁻¹⟫ = Matrix.diagonal (fun i => (e i)⁻¹)) (hv : ∀ i, Valued.v (e i) = 1) :
    d ∈ KU σ n := by
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have h1 := hv i
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hint : ∀ i, e i ∈ intL L := fun i => by
    rw [intL]
    exact (Valuation.mem_integer_iff _ _).2 (hv i).le
  have hint' : ∀ i, (e i)⁻¹ ∈ intL L := fun i => by
    rw [intL]
    exact (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hv i, inv_one])
  let D : Matrix (Fin n) (Fin n) (intL L) := Matrix.diagonal fun i => ⟨e i, hint i⟩
  let D' : Matrix (Fin n) (Fin n) (intL L) := Matrix.diagonal fun i => ⟨(e i)⁻¹, hint' i⟩
  have h1 : D * D' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Subtype.ext (by simp [hne i])
  have h2 : D' * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Subtype.ext (by simp [hne i])
  rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf]
  refine ⟨d.2, ⟨⟨D, D', h1, h2⟩, ?_⟩⟩
  rw [bc]
  ext i j
  change ((intL L).subtype.mapMatrix D) i j = ⟪d⟫ i j
  rw [hd]
  by_cases hij : i = j
  · subst hij
    simp [D]
  · simp [D, Matrix.diagonal_apply_ne _ hij]

theorem fSatake_K_int {k : GU σ n} (hk : k ∈ KU σ n) (i j : Fin n) : ⟪k⟫ i j ∈ intL L := by
  rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf] at hk
  obtain ⟨g, hg⟩ := hk.2
  rw [← hg, bc]
  exact (g.val i j).2

private lemma isBorelU_mul {b c : GU σ n} (hb : IsBorelU b) (hc : IsBorelU c) :
    IsBorelU (b * c) := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  have hC : Matrix.BlockTriangular ⟪c⟫ id := fun i j h => hc i j h
  intro i j hij
  show (⟪b⟫ * ⟪c⟫) i j = 0
  exact (hB.mul hC) hij

private lemma isBorelU_inv {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  letI : Invertible ⟪b⟫ := Units.invertible _
  have hinv : ⟪b⁻¹⟫ = (⟪b⟫)⁻¹ := by simp [Matrix.coe_units_inv]
  intro i j hij
  change ⟪b⁻¹⟫ i j = 0
  rw [hinv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hB hij

private lemma ordL_zpow_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ))) (a : ℤ) :
    ordL (ϖ ^ a) = a := by
  have hv : Valued.v (ϖ ^ a) = ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul]
    simp
  have hne : Valued.v (ϖ ^ a) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  rw [ordL, dif_neg hne]
  have h2 : WithZero.unzero hne = Multiplicative.ofAdd (-a) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv]
  rw [h2, toAdd_ofAdd, neg_neg]

private lemma isBorelU_sigma_diag_mul_opposite_diag {b : GU σ n} (hb : IsBorelU b) (i j : Fin n)
    (hij : (i : ℕ) + j + 1 = n) : σ (⟪b⟫ i i) * ⟪b⟫ j j = 1 := by
  have hB : ∀ p q : Fin n, q < p → ⟪b⟫ p q = 0 := fun p q h => hb p q h
  have hG : cT σ ⟪b⟫ * antiJ L n * ⟪b⟫ = antiJ L n := b.2
  have hG' := congrFun (congrFun hG i) j
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, antiJ] at hG'
  rw [if_pos hij, Finset.sum_eq_single j] at hG'
  · rw [Finset.sum_eq_single i, if_pos hij, mul_one] at hG'
    · exact hG'
    · intro p _ hp
      rw [if_neg (fun h => hp (Fin.ext (by omega))), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · have hlt' := Fin.lt_iff_val_lt_val.mp hlt
      rw [Finset.sum_eq_zero, zero_mul]
      intro p _
      by_cases hp : (p : ℕ) + q + 1 = n
      · rw [hB p i (Fin.lt_iff_val_lt_val.mpr (by omega)), map_zero, zero_mul]
      · rw [if_neg hp, mul_zero]
    · rw [hB q j hgt, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma isBorelU_mul_diag {A B : GU σ n} (hA : IsBorelU A) (hB : IsBorelU B) (i : Fin n) :
    ⟪A * B⟫ i i = ⟪A⟫ i i * ⟪B⟫ i i := by
  show (⟪A⟫ * ⟪B⟫) i i = _
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA i l h, zero_mul]
    · rw [hB l i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma tMat_diag_mul_opposite_diag {ϖ : L} (hϖ0 : ϖ ≠ 0) {m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ)
    (i j : Fin n) (hij : (i : ℕ) + j + 1 = n) : tMat ϖ n m a i i * tMat ϖ n m a j j = 1 := by
  simp only [tMat, Matrix.diagonal_apply_eq]
  split_ifs <;> first
    | omega
    | (simp; done)
    | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [add_neg_eq_zero]; congr 1;
        simp only [Fin.mk.injEq]; omega)
    | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [neg_add_eq_zero]; congr 1;
        simp only [Fin.mk.injEq]; omega)

private lemma sigma_tMat_diag {ϖ : L} (hσ : σ ϖ = ϖ) {m : ℕ} (a : Fin m → ℤ) (i : Fin n) :
    σ (tMat ϖ n m a i i) = tMat ϖ n m a i i := by
  simp only [tMat, Matrix.diagonal_apply_eq]
  split_ifs <;> simp [map_zpow₀, hσ]

private lemma valuation_eq_ofAdd_neg_ordL {x : L} (hx : x ≠ 0) :
    Valued.v x = ↑(Multiplicative.ofAdd (-ordL x)) := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [ordL, dif_neg hv, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

private lemma valuation_zpow_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ))) (a : ℤ) :
    Valued.v (ϖ ^ a) = ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
  congr 1
  rw [← ofAdd_zsmul]
  simp

private lemma withZero_eq_one_of_mul_self_eq_one {x : WithZero (Multiplicative ℤ)} (h : x * x = 1) : x = 1 := by
  have hx : x ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨y, rfl⟩ := WithZero.ne_zero_iff_exists.mp hx
  rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_inj] at h
  rw [← WithZero.coe_one, WithZero.coe_inj]
  have h3 := congrArg Multiplicative.toAdd h
  rw [toAdd_mul, toAdd_one] at h3
  have h2 : Multiplicative.toAdd y = 0 := by omega
  rw [← ofAdd_toAdd y, h2, ofAdd_zero]

theorem fSatake_cell_exists {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    (hm' : n ≤ 2 * m + 1) {b k : GU σ n} (hb : IsBorelU b) (hk : k ∈ KU σ n) :
    ∃ a : Fin m → ℤ, ∃ u : GU σ n, IsUnipU u ∧ ∃ k' ∈ KU σ n,
      ⟪b * k⟫ = tMat ϖ n m a * ⟪u⟫ * ⟪k'⟫ := by
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  have hσ : σ ϖ = ϖ := by
    obtain ⟨-, -, h, -⟩ := hU
    exact h
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := by
    obtain ⟨-, h, -⟩ := hU
    exact h
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hbne : ∀ i, ⟪b⟫ i i ≠ 0 := fSatake_ne_zero_of_borel hb
  obtain ⟨a, ha⟩ : ∃ a : Fin m → ℤ, ∀ i : Fin m, ∀ hi : (i : ℕ) < n,
      a i = ordL (⟪b⟫ ⟨i, hi⟩ ⟨i, hi⟩) :=
    ⟨fun i => ordL (⟪b⟫ ⟨i, lt_of_lt_of_le i.isLt (by omega)⟩ ⟨i, lt_of_lt_of_le i.isLt (by omega)⟩),
      fun i hi => rfl⟩
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  have htB : IsBorelU t := fSatake_borel_tMat ht
  have hT0 : ∀ i : Fin n, tMat ϖ n m a i i ≠ 0 := fun i h => by
    have hi := i.isLt
    have h2 := tMat_diag_mul_opposite_diag hϖ0 hm a i ⟨n - 1 - i, by omega⟩
      (by show (i : ℕ) + (n - 1 - (i : ℕ)) + 1 = n; omega)
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  obtain ⟨e, he⟩ : ∃ e : Fin n → L, ∀ i, e i = ⟪b⟫ i i * (tMat ϖ n m a i i)⁻¹ :=
    ⟨fun i => ⟪b⟫ i i * (tMat ϖ n m a i i)⁻¹, fun i => rfl⟩
  have he0 : ∀ i, e i ≠ 0 := fun i => by
    rw [he]
    exact mul_ne_zero (hbne i) (inv_ne_zero (hT0 i))
  have hrel : ∀ i j : Fin n, (i : ℕ) + j + 1 = n → σ (e i) * e j = 1 := by
    intro i j hij
    have h1 := isBorelU_sigma_diag_mul_opposite_diag hb i j hij
    have h2 := tMat_diag_mul_opposite_diag hϖ0 hm a i j hij
    rw [he, he, map_mul, map_inv₀, sigma_tMat_diag hσ a i]
    calc σ (⟪b⟫ i i) * (tMat ϖ n m a i i)⁻¹ * (⟪b⟫ j j * (tMat ϖ n m a j j)⁻¹)
        = (σ (⟪b⟫ i i) * ⟪b⟫ j j) * (tMat ϖ n m a i i * tMat ϖ n m a j j)⁻¹ := by ring
      _ = 1 := by rw [h1, h2, inv_one, mul_one]
  have hlow : ∀ i : Fin n, (i : ℕ) < m → Valued.v (e i) = 1 := by
    intro i hi
    have hT : tMat ϖ n m a i i = ϖ ^ (ordL (⟪b⟫ i i)) := by
      have h1 := fSatake_tMat_apply_lt ϖ a ⟨i, hi⟩ i.isLt
      rw [ha ⟨i, hi⟩ i.isLt] at h1
      exact h1
    rw [he, map_mul, map_inv₀, hT, valuation_zpow_uniformizer hϖ, valuation_eq_ofAdd_neg_ordL (hbne i)]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have hve : ∀ i, Valued.v (e i) = 1 := by
    intro i
    by_cases hi : (i : ℕ) < m
    · exact hlow i hi
    · have hin := i.isLt
      obtain ⟨j, hjv⟩ : ∃ j : Fin n, (j : ℕ) = n - 1 - i := ⟨⟨n - 1 - i, by omega⟩, rfl⟩
      have hij : (i : ℕ) + j + 1 = n := by omega
      have h1 := congrArg Valued.v (hrel i j hij)
      rw [map_mul, hσv, map_one] at h1
      by_cases hj : (j : ℕ) < m
      · rw [hlow j hj, mul_one] at h1
        exact h1
      · have hji : j = i := Fin.ext (by omega)
        rw [hji] at h1
        exact withZero_eq_one_of_mul_self_eq_one h1
  have hd1 : Matrix.diagonal e * Matrix.diagonal (fun i => (e i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (he0 i)
  have hd2 : Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he0 i)
  have hmemD : (⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹), hd1, hd2⟩ : GL (Fin n) L) ∈ GU σ n := by
    show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n
    rw [cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [antiJ]
    split_ifs with h
    · rw [mul_one]
      exact hrel i j h
    · simp
  let D0 : GU σ n := ⟨⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹), hd1, hd2⟩, hmemD⟩
  have hD0 : ⟪D0⟫ = Matrix.diagonal e := rfl
  have hD0i : ⟪D0⁻¹⟫ = Matrix.diagonal (fun i => (e i)⁻¹) := rfl
  have hD0K : D0 ∈ KU σ n := fSatake_diag_mem_K hD0 hD0i hve
  have hD0B : IsBorelU D0 := fSatake_borel_of_diag hD0
  have htinv : ∀ i, ⟪t⁻¹⟫ i i = (tMat ϖ n m a i i)⁻¹ := fun i => by
    have h1 := isBorelU_mul_diag (isBorelU_inv htB) htB i
    rw [inv_mul_cancel, ht] at h1
    have h0 : ⟪(1 : GU σ n)⟫ i i = 1 := by simp
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have huB : IsBorelU (t⁻¹ * b * D0⁻¹) :=
    isBorelU_mul (isBorelU_mul (isBorelU_inv htB) hb) (isBorelU_inv hD0B)
  have hudiag : ∀ i, ⟪t⁻¹ * b * D0⁻¹⟫ i i = 1 := fun i => by
    rw [isBorelU_mul_diag (isBorelU_mul (isBorelU_inv htB) hb) (isBorelU_inv hD0B),
      isBorelU_mul_diag (isBorelU_inv htB) hb, htinv, hD0i, Matrix.diagonal_apply_eq, he]
    field_simp [hbne i, hT0 i]
  have huU : IsUnipU (t⁻¹ * b * D0⁻¹) := by
    unfold IsUnipU
    exact ⟨huB, hudiag⟩
  refine ⟨a, t⁻¹ * b * D0⁻¹, huU, D0 * k, (KU σ n).mul_mem hD0K hk, ?_⟩
  have hgrp : b * k = t * (t⁻¹ * b * D0⁻¹) * (D0 * k) := by group
  rw [hgrp]
  show ⟪t⟫ * ⟪t⁻¹ * b * D0⁻¹⟫ * ⟪D0 * k⟫ = _
  rw [ht]

private lemma tMat_exponent_le_of_eq_unip_mul_KU {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    {a a' : Fin m → ℤ} {u u' k k' : GU σ n} (hu : IsUnipU u) (hu' : IsUnipU u')
    (hk : k ∈ KU σ n) (hk' : k' ∈ KU σ n)
    (h : tMat ϖ n m a * ⟪u⟫ * ⟪k⟫ = tMat ϖ n m a' * ⟪u'⟫ * ⟪k'⟫) (i : Fin m) : a' i ≤ a i := by
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  obtain ⟨t', ht'⟩ := fSatake_tMat_exists hU hm a'
  obtain ⟨huB, hu1⟩ := hu
  obtain ⟨huB', hu1'⟩ := hu'
  have hgeq : t * u * k = t' * u' * k' := by
    apply Subtype.ext
    apply Units.ext
    show ⟪t⟫ * ⟪u⟫ * ⟪k⟫ = ⟪t'⟫ * ⟪u'⟫ * ⟪k'⟫
    rw [ht, ht']
    exact h
  have hq : (t' * u')⁻¹ * (t * u) = k' * k⁻¹ := by
    calc (t' * u')⁻¹ * (t * u) = (t' * u')⁻¹ * (t * u * k) * k⁻¹ := by group
      _ = (t' * u')⁻¹ * (t' * u' * k') * k⁻¹ := by rw [hgeq]
      _ = k' * k⁻¹ := by group
  have hK : k' * k⁻¹ ∈ KU σ n := (KU σ n).mul_mem hk' ((KU σ n).inv_mem hk)
  have hi : (i : ℕ) < n := lt_of_lt_of_le i.isLt (by omega)
  have hint := fSatake_K_int hK ⟨i, hi⟩ ⟨i, hi⟩
  rw [← hq] at hint
  have htB := fSatake_borel_tMat ht
  have htB' := fSatake_borel_tMat ht'
  have hB1 : IsBorelU (t * u) := isBorelU_mul htB huB
  have hB2 : IsBorelU (t' * u') := isBorelU_mul htB' huB'
  have hd1 : ⟪t * u⟫ ⟨i, hi⟩ ⟨i, hi⟩ = ϖ ^ (a i) := by
    rw [isBorelU_mul_diag htB huB, hu1, mul_one, ht]
    exact fSatake_tMat_apply_lt ϖ a i hi
  have hd2 : ⟪t' * u'⟫ ⟨i, hi⟩ ⟨i, hi⟩ = ϖ ^ (a' i) := by
    rw [isBorelU_mul_diag htB' huB', hu1', mul_one, ht']
    exact fSatake_tMat_apply_lt ϖ a' i hi
  have hd2i : ⟪(t' * u')⁻¹⟫ ⟨i, hi⟩ ⟨i, hi⟩ = (ϖ ^ (a' i))⁻¹ := by
    have h1 := isBorelU_mul_diag (isBorelU_inv hB2) hB2 ⟨i, hi⟩
    rw [inv_mul_cancel, hd2] at h1
    have h0 : ⟪(1 : GU σ n)⟫ ⟨i, hi⟩ ⟨i, hi⟩ = 1 := by simp
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  rw [isBorelU_mul_diag (isBorelU_inv hB2) hB1, hd2i, hd1, ← zpow_neg, ← zpow_add₀ hϖ0] at hint
  rw [intL, Valuation.mem_integer_iff, valuation_zpow_uniformizer hϖ] at hint
  rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le] at hint
  omega

theorem fSatake_cell_unique {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    {a a' : Fin m → ℤ} {u u' k k' : GU σ n} (hu : IsUnipU u) (hu' : IsUnipU u')
    (hk : k ∈ KU σ n) (hk' : k' ∈ KU σ n)
    (h : tMat ϖ n m a * ⟪u⟫ * ⟪k⟫ = tMat ϖ n m a' * ⟪u'⟫ * ⟪k'⟫) : a = a' := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact absurd this WithZero.zero_ne_coe
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  obtain ⟨t', ht'⟩ := fSatake_tMat_exists hU hm a'
  have htb := fSatake_borel_tMat ht
  have htb' := fSatake_borel_tMat ht'
  have hx : t * u * k = t' * u' * k' := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, ht, ht']
    exact h
  have hwk : (t' * u')⁻¹ * (t * u) = k' * k⁻¹ := by
    calc (t' * u')⁻¹ * (t * u) = (t' * u')⁻¹ * (t * u * k) * k⁻¹ := by group
      _ = (t' * u')⁻¹ * (t' * u' * k') * k⁻¹ := by rw [hx]
      _ = k' * k⁻¹ := by group
  have hwK : (t' * u')⁻¹ * (t * u) ∈ KU σ n := by rw [hwk]; exact mul_mem hk' (inv_mem hk)
  have hb1 := fSatake_borel_mul htb hu.1
  have hb2 := fSatake_borel_mul htb' hu'.1
  have hwb : IsBorelU ((t' * u')⁻¹ * (t * u)) := fSatake_borel_mul (fSatake_borel_inv hb2) hb1
  have htu : t * u = (t' * u') * ((t' * u')⁻¹ * (t * u)) := by group
  funext j
  have hj : (j : ℕ) < n := by omega
  have hdiag : ⟪t * u⟫ ⟨j, hj⟩ ⟨j, hj⟩ = ⟪(t' * u') * ((t' * u')⁻¹ * (t * u))⟫ ⟨j, hj⟩ ⟨j, hj⟩ :=
    congrArg (fun z : GU σ n => ⟪z⟫ ⟨j, hj⟩ ⟨j, hj⟩) htu
  rw [fSatake_borel_diag_mul hb2 hwb, fSatake_borel_diag_mul htb hu.1,
    fSatake_borel_diag_mul htb' hu'.1, hu.2, hu'.2, ht, ht', mul_one, mul_one,
    fSatake_tMat_apply_lt ϖ a j hj, fSatake_tMat_apply_lt ϖ a' j hj] at hdiag
  set w := (t' * u')⁻¹ * (t * u)
  have hw0 : ⟪w⟫ ⟨j, hj⟩ ⟨j, hj⟩ ≠ 0 := fSatake_ne_zero_of_borel hwb _
  have hwr0 := fSatake_ne_zero_of_borel hwb (⟨j, hj⟩ : Fin n).rev
  have hpair := congrArg ordL (fSatake_unit_diag hwb ⟨j, hj⟩)
  rw [fSatake_ord_mul ((map_ne_zero σ).2 hw0) hwr0, fSatake_ord_of_v (hU.2.1 _),
    fSatake_ord_one] at hpair
  have hn1 := fSatake_ord_nonneg hw0 (fSatake_K_int hwK _ _)
  have hn2 := fSatake_ord_nonneg hwr0 (fSatake_K_int hwK _ _)
  have h3 := congrArg ordL hdiag
  rw [fSatake_ord_mul (zpow_ne_zero _ hϖ0) hw0, fSatake_ord_zpow hU.2.2.2.1,
    fSatake_ord_zpow hU.2.2.2.1] at h3
  omega

theorem fSatake_phi_cell {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    {α : Fin m → ℂ} {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) {x u k : GU σ n}
    {a : Fin m → ℤ} (hu : IsUnipU u) (hk : k ∈ KU σ n)
    (hx : ⟪x⟫ = tMat ϖ n m a * ⟪u⟫ * ⟪k⟫) :
    φ x = (∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      φ 1 := by
  obtain ⟨huB, hu1⟩ := hu
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  have htB : IsBorelU t := fSatake_borel_tMat ht
  have hxe : x = t * u * k := by
    apply Subtype.ext
    apply Units.ext
    show ⟪x⟫ = ⟪t⟫ * ⟪u⟫ * ⟪k⟫
    rw [hx, ht]
  have h1 := hφ (t * u) 1 k (isBorelU_mul htB huB) hk
  rw [mul_one] at h1
  rw [hxe, h1]
  congr 1
  rw [chiDeltaU]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi : (i : ℕ) < n := lt_of_lt_of_le i.isLt (by omega)
  have hd : ⟪t * u⟫ ⟨i, hi⟩ ⟨i, hi⟩ = ϖ ^ (a i) := by
    show (⟪t⟫ * ⟪u⟫) ⟨i, hi⟩ ⟨i, hi⟩ = _
    rw [ht, tMat, Matrix.diagonal_mul, hu1, mul_one]
    simp [i.isLt]
  rw [dif_pos hi, hd, ordL_zpow_uniformizer hϖ]

theorem fSatake_vanish (hSph : SphericalExistsU) [CompleteSpace L] {ϖ : L} {q m : ℕ}
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) {α : Fin m → ℂ}
    (hα : ∀ i, α i ≠ 0) {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (x : GU σ n)
    (hx : ¬ ∃ b k : GU σ n, IsBorelU b ∧ k ∈ KU σ n ∧ x = b * k) : φ x = 0 := by
  classical
  obtain ⟨φ0, -, -, huniq⟩ := hSph L ϖ σ q n m hU hm hm' α hα
  have hP : ∀ b g k : GU σ n, IsBorelU b → k ∈ KU σ n →
      ((∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ b * g * k = b' * k') ↔
        (∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k')) := by
    intro b g k hb hk
    constructor
    · rintro ⟨b', k', hb', hk', he⟩
      refine ⟨b⁻¹ * b', k' * k⁻¹, isBorelU_mul (isBorelU_inv hb) hb',
        (KU σ n).mul_mem hk' ((KU σ n).inv_mem hk), ?_⟩
      calc g = b⁻¹ * (b * g * k) * k⁻¹ := by group
        _ = b⁻¹ * b' * (k' * k⁻¹) := by rw [he]; group
    · rintro ⟨b', k', hb', hk', he⟩
      refine ⟨b * b', k' * k, isBorelU_mul hb hb', (KU σ n).mul_mem hk' hk, ?_⟩
      rw [he]
      group
  let ψ : GU σ n → ℂ := fun g =>
    if (∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k') then φ g else 0
  have hψ : IsSphericalU q α ψ := by
    intro b g k hb hk
    by_cases hg : ∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ g = b' * k'
    · have h1 := (hP b g k hb hk).2 hg
      simp only [ψ, if_pos h1, if_pos hg]
      exact hφ b g k hb hk
    · have h1 : ¬ ∃ b' k' : GU σ n, IsBorelU b' ∧ k' ∈ KU σ n ∧ b * g * k = b' * k' :=
        fun h => hg ((hP b g k hb hk).1 h)
      simp only [ψ, if_neg h1, if_neg hg, mul_zero]
  have hψ1 : ψ 1 = φ 1 := by
    simp only [ψ]
    exact if_pos ⟨1, 1, fSatake_borel_one, (KU σ n).one_mem, by simp⟩
  have hψx : ψ x = 0 := by
    simp only [ψ]
    exact if_neg hx
  have e1 : ψ x = ψ 1 * φ0 x := congrFun (huniq ψ hψ) x
  have e2 : φ x = φ 1 * φ0 x := congrFun (huniq φ hφ) x
  rw [e2, ← hψ1, ← e1, hψx]

end Formalism.UG.P
