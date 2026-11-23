import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardSumNormFibres

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns

open Matrix

variable {k : Type*} [Field k]

def cj {n n' : Type*} (σ : k ≃+* k) (X : Matrix n n' k) : Matrix n' n k := (X.map σ).transpose

theorem cj_apply {n n' : Type*} (σ : k ≃+* k) (X : Matrix n n' k) (i : n') (j : n) :
    cj σ X i j = σ (X j i) := rfl

theorem cj_mul {n n' n'' : Type*} [Fintype n'] (σ : k ≃+* k) (X : Matrix n n' k)
    (Y : Matrix n' n'' k) : cj σ (X * Y) = cj σ Y * cj σ X := by
  ext i j
  simp [cj_apply, Matrix.mul_apply, mul_comm]

theorem cj_one {n : Type*} [DecidableEq n] (σ : k ≃+* k) : cj σ (1 : Matrix n n k) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cj_apply]
  · simp [cj_apply, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem exists_refl {n : Type*} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (x y : n → k) (hx : ∑ i, σ (x i) * x i = 1)
    (hy : ∑ i, σ (y i) * y i = 1) (hxy : ∑ i, σ (y i) * x i ≠ 1) :
    ∃ g : Matrix n n k, cj σ g * g = 1 ∧ g *ᵥ x = y := by
  set u : n → k := x - y with hu
  set a : k := ∑ i, σ (u i) * x i with ha
  have ha1 : a = 1 - ∑ i, σ (y i) * x i := by
    simp only [ha, hu, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib, hx]
  have ha0 : a ≠ 0 := by
    rw [ha1]; exact sub_ne_zero.mpr (Ne.symm hxy)
  have hsa0 : σ a ≠ 0 := by simpa using ha0
  have hsa : σ a = 1 - ∑ i, σ (x i) * y i := by
    rw [ha1]; simp [map_sum, hσ, mul_comm]
  have hn : ∑ i, σ (u i) * u i = a + σ a := by
    rw [hsa, ha1]
    simp only [hu, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib, hx, hy]
    ring
  set P : Matrix n n k := vecMulVec u (fun i => σ (u i)) with hP
  have hPP : P * P = (a + σ a) • P := by
    rw [hP, Matrix.vecMulVec_mul_vecMulVec, ← hn]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]
    ring
  have hcP : cj σ P = P := by
    ext i j
    simp [cj_apply, hP, vecMulVec_apply, hσ, mul_comm]
  refine ⟨1 - a⁻¹ • P, ?_, ?_⟩
  · have hc : cj σ (1 - a⁻¹ • P) = 1 - (σ a)⁻¹ • P := by
      ext i j
      have := congrFun (congrFun hcP i) j
      have h1 := congrFun (congrFun (cj_one (n := n) σ) i) j
      simp only [cj_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul,
        map_inv₀] at this h1 ⊢
      rw [this, h1]
    rw [hc, sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP]
    have : (σ a)⁻¹ * a⁻¹ * (a + σ a) = a⁻¹ + (σ a)⁻¹ := by
      field_simp
      ring
    rw [smul_smul, this, add_smul]
    abel
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP, Matrix.vecMulVec_mulVec]
    have : (fun i => σ (u i)) ⬝ᵥ x = a := rfl
    rw [this]
    ext i
    simp [hu, ha0]

theorem cj_cj {n n' : Type*} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (X : Matrix n n' k) :
    cj σ (cj σ X) = X := by
  ext i j
  simp [cj_apply, hσ]

theorem exists_col {m : ℕ} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (x : Fin (m + 1) → k) (hx : ∑ i, σ (x i) * x i = 1) :
    ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) k, cj σ g * g = 1 ∧ ∀ i, g i 0 = x i := by
  have he : ∑ i, σ ((Pi.single 0 1 : Fin (m + 1) → k) i) * (Pi.single 0 1 : Fin (m + 1) → k) i = 1 := by
    rw [Finset.sum_eq_single 0] <;> simp +contextual
  have hs : ∀ y : Fin (m + 1) → k, ∑ i, σ (y i) * (Pi.single 0 1 : Fin (m + 1) → k) i = σ (y 0) := by
    intro y
    rw [Finset.sum_eq_single 0] <;> simp +contextual
  by_cases h1 : σ (x 0) = 1
  · obtain ⟨t, ht⟩ := hne
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht
    have hst0 : σ t ≠ 0 := by simpa using ht0
    set ζ : k := σ t / t with hζ
    have hζ0 : ζ ≠ 0 := div_ne_zero hst0 ht0
    have hsζ : σ ζ = t / σ t := by simp [hζ, hσ]
    have hN : σ ζ * ζ = 1 := by
      rw [hsζ, hζ]; field_simp
    have hsζ1 : σ ζ ≠ 1 := by
      rw [hsζ]
      intro h
      rw [div_eq_one_iff_eq hst0] at h
      exact ht h.symm
    obtain ⟨g, hg, hgx⟩ := exists_refl σ hσ (Pi.single 0 1) (fun i => ζ * x i) he
      (by
        have : ∀ i, σ (ζ * x i) * (ζ * x i) = (σ ζ * ζ) * (σ (x i) * x i) := by
          intro i; rw [map_mul]; ring
        simp only [this, ← Finset.mul_sum, hx, hN, mul_one])
      (by rw [hs, map_mul, h1, mul_one]; exact hsζ1)
    refine ⟨ζ⁻¹ • g, ?_, ?_⟩
    · have hc : cj σ (ζ⁻¹ • g) = (σ ζ)⁻¹ • cj σ g := by
        ext i j
        simp [cj_apply]
      rw [hc, smul_mul_smul_comm, hg, ← mul_inv, hN, inv_one, one_smul]
    · intro i
      have := congrFun hgx i
      rw [Matrix.mulVec_single_one] at this
      simp only [Matrix.col_apply] at this
      simp [this, hζ0]
  · obtain ⟨g, hg, hgx⟩ := exists_refl σ hσ (Pi.single 0 1) x he hx (by rw [hs]; exact h1)
    refine ⟨g, hg, fun i => ?_⟩
    have := congrFun hgx i
    rw [Matrix.mulVec_single_one] at this
    simpa using this

def emb {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => Y i' j') j) i

@[simp] theorem emb_zero_zero {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) : emb Y 0 0 = 1 := rfl
@[simp] theorem emb_zero_succ {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) (j : Fin m) :
    emb Y 0 j.succ = 0 := rfl
@[simp] theorem emb_succ_zero {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) (i : Fin m) :
    emb Y i.succ 0 = 0 := rfl
@[simp] theorem emb_succ_succ {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) (i j : Fin m) :
    emb Y i.succ j.succ = Y i j := rfl

theorem one_succ_succ {m : ℕ} (i j : Fin m) :
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.succ j.succ = (1 : Matrix (Fin m) (Fin m) k) i j := by
  simp [Matrix.one_apply]

theorem emb_unitary {m : ℕ} (σ : k ≃+* k) (Y : Matrix (Fin m) (Fin m) k) (h : cj σ Y * Y = 1) :
    cj σ (emb Y) * emb Y = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, (Fin.succ_ne_zero j').symm]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, Fin.succ_ne_zero i']
  · have := congrFun (congrFun h i') j'
    rw [one_succ_succ, ← this]
    simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply]

theorem eq_emb {m : ℕ} (σ : k ≃+* k) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
    (h : cj σ Z * Z = 1) (h0 : Z 0 0 = 1) (hs : ∀ i : Fin m, Z i.succ 0 = 0) :
    Z = emb (Z.submatrix Fin.succ Fin.succ) ∧
      cj σ (Z.submatrix Fin.succ Fin.succ) * Z.submatrix Fin.succ Fin.succ = 1 := by
  have hrow : ∀ j : Fin m, Z 0 j.succ = 0 := by
    intro j
    have := congrFun (congrFun h 0) j.succ
    simpa [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, h0, hs, Matrix.one_apply,
      (Fin.succ_ne_zero j).symm] using this
  constructor
  · ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp [h0]
    · simp [hrow]
    · simp [hs]
    · simp
  · ext i j
    have := congrFun (congrFun h i.succ) j.succ
    rw [one_succ_succ] at this
    rw [← this]
    simp [Matrix.mul_apply, Fin.sum_univ_succ, cj_apply, hrow]

theorem card_succ {m : ℕ} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k // cj σ X * X = 1} =
      Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} *
        Nat.card {X : Matrix (Fin m) (Fin m) k // cj σ X * X = 1} := by
  choose g hg hgc using fun x : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} =>
    exists_col σ hσ hne x.1 x.2
  have hg' : ∀ x, g x * cj σ (g x) = 1 := fun x => mul_eq_one_comm.mp (hg x)
  have hcol : ∀ x (Y : Matrix (Fin m) (Fin m) k) i, (g x * emb Y) i 0 = x.1 i := by
    intro x Y i
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hgc]
  let Φ : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} ×
      {X : Matrix (Fin m) (Fin m) k // cj σ X * X = 1} →
      {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k // cj σ X * X = 1} := fun p =>
    ⟨g p.1 * emb p.2.1, by
      rw [cj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cj σ (g p.1)), hg, Matrix.one_mul]
      exact emb_unitary σ _ p.2.2⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨x, Y⟩ ⟨x', Y'⟩ h
      have h1 : g x * emb Y.1 = g x' * emb Y'.1 := congrArg Subtype.val h
      have hxx : x = x' := by
        apply Subtype.ext
        funext i
        rw [← hcol x Y.1 i, h1, hcol]
      subst hxx
      have h2 : emb Y.1 = emb Y'.1 := by
        have := congrArg (fun M => cj σ (g x) * M) h1
        simpa only [← Matrix.mul_assoc, hg, Matrix.one_mul] using this
      have hYY : Y = Y' := by
        apply Subtype.ext
        ext i j
        exact congrFun (congrFun h2 i.succ) j.succ
      rw [hYY]
    · rintro ⟨X, hX⟩
      have hx : ∑ i, σ (X i 0) * X i 0 = 1 := by
        have := congrFun (congrFun hX 0) 0
        simpa [Matrix.mul_apply, cj_apply] using this
      set x : {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} := ⟨fun i => X i 0, hx⟩ with hxdef
      set Z := cj σ (g x) * X with hZ
      have hZu : cj σ Z * Z = 1 := by
        rw [hZ, cj_mul, cj_cj σ hσ, Matrix.mul_assoc, ← Matrix.mul_assoc (g x), hg',
          Matrix.one_mul, hX]
      have hZc : ∀ i, Z i 0 = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i 0 := by
        intro i
        rw [← hg x, hZ]
        simp only [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hgc x l]
      obtain ⟨hE, hU⟩ := eq_emb σ Z hZu (by rw [hZc]; simp)
        (fun i => by rw [hZc]; simp [Fin.succ_ne_zero i])
      refine ⟨(x, ⟨_, hU⟩), Subtype.ext ?_⟩
      change g x * emb (Z.submatrix Fin.succ Fin.succ) = X
      rw [← hE, hZ, ← Matrix.mul_assoc, hg', Matrix.one_mul]
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm

end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns

namespace Formalism.HermitianLattices.Ext.L3

theorem card_unitary_fin {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2) (m : ℕ) :
    (Nat.card {X : Matrix (Fin m) (Fin m) k // (X.map σ).transpose * X = 1} : ℝ) =
      (q : ℝ) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (1 - (-(q : ℝ))⁻¹ ^ j) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have h1 : 0 < Fintype.card k := Fintype.card_pos
    rw [hq] at h1
    have : q ≠ 0 := by
      rintro rfl
      simp at h1
    exact_mod_cast this
  induction m with
  | zero =>
    have : Nat.card {X : Matrix (Fin 0) (Fin 0) k // (X.map σ).transpose * X = 1} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨1, Subsingleton.elim _ _⟩⟩⟩
    rw [this]
    simp
  | succ m ih =>
    have h1 := FiniteUnitaryColumns.card_succ (m := m) σ hσ hne
    have h2 := card_herm_norm_eq σ hσ hne q hq (m + 1) (by omega) 1 (map_one σ) one_ne_zero
    have h2' : (Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} : ℝ) =
        (q : ℝ) ^ m * ((q : ℝ) ^ (m + 1) - (-1) ^ (m + 1)) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h2
      simpa using this
    have h1' : (Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k //
        (X.map σ).transpose * X = 1} : ℝ) =
        (Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} : ℝ) *
          (Nat.card {X : Matrix (Fin m) (Fin m) k // (X.map σ).transpose * X = 1} : ℝ) := by
      exact_mod_cast h1
    rw [h1', h2', ih, Finset.prod_Icc_succ_top (by omega)]
    have h3 : (q : ℝ) ^ ((m + 1) ^ 2) = (q : ℝ) ^ (m ^ 2) * ((q : ℝ) ^ m * (q : ℝ) ^ (m + 1)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    have h4 : (q : ℝ) ^ (m + 1) * (1 - (-(q : ℝ))⁻¹ ^ (m + 1)) =
        (q : ℝ) ^ (m + 1) - (-1) ^ (m + 1) := by
      have : (-(q : ℝ))⁻¹ = (-1) * (q : ℝ)⁻¹ := by
        rw [neg_mul, one_mul, inv_neg]
      rw [this, mul_pow, mul_sub, mul_one, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hq0, one_pow,
        mul_one]
    rw [h3, ← h4]
    ring

theorem card_GL_fin {k : Type*} [Field k] [Fintype k] (q : ℕ) (hq : Fintype.card k = q) (m : ℕ) :
    (Nat.card (GL (Fin m) k) : ℝ) = (q : ℝ) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (1 - (q : ℝ)⁻¹ ^ j) := by
  subst hq
  set q : ℕ := Fintype.card k with hqd
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hq0 : (q : ℝ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  rw [Matrix.card_GL_field, Fin.prod_univ_eq_prod_range (fun i => q ^ m - q ^ i) m, Nat.cast_prod]
  have h1 : ∀ i ∈ Finset.range m, ((q ^ m - q ^ i : ℕ) : ℝ) =
      (q : ℝ) ^ m * (1 - (q : ℝ)⁻¹ ^ (m - 1 - i + 1)) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq1 him.le), Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
    congr 1
    have : m = i + (m - 1 - i + 1) := by omega
    conv_rhs => rw [this, pow_add]
    have h5 : m - 1 - i + 1 = i + (m - 1 - i + 1) - 1 - i + 1 := by omega
    rw [← h5, mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, mul_one]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul, ← sq, Finset.prod_range_reflect (fun j => 1 - (q : ℝ)⁻¹ ^ (j + 1)) m]
  congr 1
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' (fun j => 1 - (q : ℝ)⁻¹ ^ j) 0 m 1]
  rfl

end Formalism.HermitianLattices.Ext.L3
