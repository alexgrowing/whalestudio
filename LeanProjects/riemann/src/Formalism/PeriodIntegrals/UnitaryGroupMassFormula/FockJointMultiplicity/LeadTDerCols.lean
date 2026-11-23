import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurElim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistWt

noncomputable section

open MvPolynomial

namespace PI.FJMX

section Gen

variable {A : Type*} [CommRing A] [Algebra ℂ A] {m k : ℕ}

theorem leadT_der_rows' (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (t : ℕ)
    (h : ∀ i₀ : Fin m, i₀.val < t → (∀ j : Fin k, j.val < t → D (M i₀ j) = 0) ∨
      ∃ i₁ : Fin m, i₁.val < t ∧ i₁ ≠ i₀ ∧ ∃ e : A, ∀ j : Fin k, j.val < t → D (M i₀ j) = e * M i₁ j) :
    D (PI.FJM.leadT M t) = 0 := by
  unfold PI.FJM.leadT
  split_ifs with hh
  · apply deriv_det_eq_zero_rows
    intro i
    rcases h (Fin.castLE hh.1 i) (by simp) with h0 | ⟨i₁, hi₁, hne, e, he⟩
    · left
      intro j
      simp only [Matrix.submatrix_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨i₁.val, hi₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro j
        simp only [Matrix.submatrix_apply]
        rw [he _ (by simp)]
        rfl
  · simp

theorem leadT_der_cols' (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (t : ℕ)
    (h : ∀ j₀ : Fin k, j₀.val < t → (∀ i : Fin m, i.val < t → D (M i j₀) = 0) ∨
      ∃ j₁ : Fin k, j₁.val < t ∧ j₁ ≠ j₀ ∧ ∃ e : A, ∀ i : Fin m, i.val < t → D (M i j₀) = e * M i j₁) :
    D (PI.FJM.leadT M t) = 0 := by
  unfold PI.FJM.leadT
  split_ifs with hh
  · apply deriv_det_eq_zero
    intro j
    rcases h (Fin.castLE hh.2 j) (by simp) with h0 | ⟨j₁, hj₁, hne, e, he⟩
    · left
      intro i
      simp only [Matrix.submatrix_apply]
      exact h0 _ (by simp)
    · right
      refine ⟨⟨j₁.val, hj₁⟩, ?_, e, ?_⟩
      · intro hc
        apply hne
        ext
        simp [← hc]
      · intro i
        simp only [Matrix.submatrix_apply]
        rw [he _ (by simp)]
        rfl
  · simp

theorem shapeProd_der' (D : Derivation ℂ A A) (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ t, D (PI.FJM.leadT M t) = 0) : D (PI.FJM.shapeProd M α) = 0 := by
  unfold PI.FJM.shapeProd
  apply deriv_prod_eq_zero
  intro t _
  exact deriv_pow_eq_zero _ _ _ (h _)

end Gen

section Block

variable {σ : Type*} {m n : ℕ}

theorem derSum_apply {ι : Type*} (t : Finset ι) (D : ι → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (f : MvPolynomial σ ℂ) : (∑ c ∈ t, D c) f = ∑ c ∈ t, D c f := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

def rowD (ι : Fin m × Fin n → σ) (a b : Fin m) : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ k : Fin n, (X (ι (a, k)) : MvPolynomial σ ℂ) • pderiv (ι (b, k))

def colD (ι : Fin m × Fin n → σ) (c d : Fin n) : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ i : Fin m, (X (ι (i, c)) : MvPolynomial σ ℂ) • pderiv (ι (i, d))

theorem bRow_eq_rowD (ι : Fin m × Fin n → σ) (a b : Fin m) (f : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b f = rowD ι a b f := by
  rw [PI.FJM.bRow, rowD, derSum_apply, LinearMap.sum_apply]
  rfl

theorem bCol_eq_colD (ι : Fin m × Fin n → σ) (c d : Fin n) (f : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d f = colD ι c d f := by
  rw [PI.FJM.bCol, colD, derSum_apply, LinearMap.sum_apply]
  rfl

theorem rowD_X (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (a b i : Fin m) (j : Fin n) :
    rowD ι a b (X (ι (i, j))) = if i = b then X (ι (a, j)) else 0 := by
  classical
  rw [rowD, derSum_apply, Finset.sum_eq_single j]
  · by_cases h : i = b
    · subst h; simp
    · have : ι (i, j) ≠ ι (b, j) := fun e => h (by have := hι e; simp at this; exact this)
      simp [h, pderiv_X_of_ne this]
  · intro k _ hk
    have : ι (i, j) ≠ ι (b, k) := fun e => hk (by have := hι e; simp at this; exact this.2.symm)
    simp [pderiv_X_of_ne this]
  · simp

theorem colD_X (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (i : Fin m) (j : Fin n) :
    colD ι c d (X (ι (i, j))) = if j = d then X (ι (i, c)) else 0 := by
  classical
  rw [colD, derSum_apply, Finset.sum_eq_single i]
  · by_cases h : j = d
    · subst h; simp
    · have : ι (i, j) ≠ ι (i, d) := fun e => h (by have := hι e; simp at this; exact this)
      simp [h, pderiv_X_of_ne this]
  · intro k _ hk
    have : ι (i, j) ≠ ι (k, d) := fun e => hk (by have := hι e; simp at this; exact this.1.symm)
    simp [pderiv_X_of_ne this]
  · simp

abbrev blkM (ι : Fin m × Fin n → σ) : Matrix (Fin m) (Fin n) (MvPolynomial σ ℂ) :=
  Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)

theorem shapeProd_hwb (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (α : List ℕ) :
    PI.FJMB.HWB ι (PI.FJM.shapeProd (blkM ι) α) := by
  refine ⟨fun a b hab => ?_, fun c d hcd => ?_⟩
  · rw [bRow_eq_rowD]
    apply shapeProd_der'
    intro t
    apply leadT_der_rows'
    intro i₀ hi₀
    by_cases hb : i₀ = b
    · right
      subst hb
      refine ⟨a, by omega, ne_of_lt hab, 1, fun j _ => ?_⟩
      simp [blkM, rowD_X ι hι]
    · left
      intro j _
      simp [blkM, rowD_X ι hι, hb]
  · rw [bCol_eq_colD]
    apply shapeProd_der'
    intro t
    apply leadT_der_cols'
    intro j₀ hj₀
    by_cases hd : j₀ = d
    · right
      subst hd
      refine ⟨c, by omega, ne_of_lt hcd, 1, fun i _ => ?_⟩
      simp [blkM, colD_X ι hι]
    · left
      intro i _
      simp [blkM, colD_X ι hι, hd]

end Block

section Diag

variable {σ : Type*} {m : ℕ}

theorem prod_castLE_eq {M : Type*} [CommMonoid M] {t : ℕ} (h : t ≤ m) (g : Fin m → M) :
    ∏ i : Fin t, g (Fin.castLE h i) = ∏ i : Fin m, g i ^ (if i.val < t then 1 else 0) := by
  classical
  have e1 : ∏ i : Fin m, g i ^ (if i.val < t then 1 else 0) =
      ∏ i : Fin m, (if i.val < t then g i else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  rw [e1, ← Finset.prod_filter]
  have e2 : (Finset.univ.filter fun i : Fin m => i.val < t) = Finset.univ.map (Fin.castLEEmb h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
    · rintro ⟨a, -, rfl⟩
      simp
  rw [e2, Finset.prod_map]
  rfl

theorem leadT_diag (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (t : ℕ) (ht : t ≤ m) :
    aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.leadT (blkM ι) t) =
      ∏ i : Fin m, X (ι (i, i)) ^ (if i.val < t then 1 else 0) := by
  classical
  unfold PI.FJM.leadT
  rw [dif_pos ⟨ht, ht⟩, AlgHom.map_det]
  have hD : (aeval (PI.FJMB.killS (PI.FJMB.offD ι))).mapMatrix ((blkM ι).submatrix (Fin.castLE ht) (Fin.castLE ht)) =
      Matrix.diagonal (fun i : Fin t => (X (ι (Fin.castLE ht i, Fin.castLE ht i)) : MvPolynomial σ ℂ)) := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, blkM, Matrix.of_apply, aeval_X,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      have : ι (Fin.castLE ht i, Fin.castLE ht i) ∉ PI.FJMB.offD ι := by
        rintro ⟨i', k', he, hne⟩
        have := hι he
        simp only [Prod.mk.injEq] at this
        apply hne
        rw [this.1, this.2]
      simp [PI.FJMB.killS, this]
    · have : ι (Fin.castLE ht i, Fin.castLE ht j) ∈ PI.FJMB.offD ι := by
        refine ⟨Fin.castLE ht i, Fin.castLE ht j, rfl, ?_⟩
        simp only [Fin.coe_castLE]
        exact fun h => hij (Fin.ext h)
      simp [PI.FJMB.killS, this, hij]
  rw [hD, Matrix.det_diagonal]
  exact prod_castLE_eq ht (fun i => (X (ι (i, i)) : MvPolynomial σ ℂ))

theorem shapeProd_diag (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (α : Fin m → ℕ) (hα : Antitone α) :
    aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.shapeProd (blkM ι) (List.ofFn α)) =
      ∏ i, X (ι (i, i)) ^ α i := by
  classical
  have hpw : (List.ofFn α).Pairwise (· ≥ ·) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hα hij.le
  unfold PI.FJM.shapeProd
  rw [map_prod]
  have e1 : ∀ t ∈ Finset.range (List.ofFn α).length,
      aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.leadT (blkM ι) (t + 1) ^
        ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) =
      ∏ i : Fin m, X (ι (i, i)) ^ ((if i.val < t + 1 then 1 else 0) *
        ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) := by
    intro t ht
    simp only [List.length_ofFn, Finset.mem_range] at ht
    rw [map_pow, leadT_diag ι hι (t + 1) (by omega), ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [pow_mul]
  rw [Finset.prod_congr rfl e1, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [List.length_ofFn]
  have := shape_sum (List.ofFn α) hpw i.val
  rw [List.length_ofFn] at this
  simp only [smul_eq_mul] at this
  rw [show (∑ t ∈ Finset.range m, (if i.val < t + 1 then 1 else 0) *
      ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0)) =
      ∑ t ∈ Finset.range m, ((List.ofFn α).getD t 0 - (List.ofFn α).getD (t + 1) 0) *
        (if i.val < t + 1 then 1 else 0) from Finset.sum_congr rfl (fun _ _ => mul_comm _ _), this]
  simp

end Diag

end PI.FJMX
