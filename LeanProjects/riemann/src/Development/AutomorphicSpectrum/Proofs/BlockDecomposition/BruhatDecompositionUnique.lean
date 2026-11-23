import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.CompanionTheory.BruhatInv

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

def ind (K : Type) [Field K] {ι : Type} [DecidableEq ι] (p : ι → Prop) [DecidablePred p] :
    Matrix ι ι K :=
  Matrix.diagonal fun i => if p i then 1 else 0

theorem ind_mul_apply (p : ι → Prop) [DecidablePred p] (A : Matrix ι ι K) (i j : ι) :
    (ind K p * A) i j = (if p i then 1 else 0) * A i j := by
  simp [ind, Matrix.diagonal_mul]

theorem mul_ind_apply (p : ι → Prop) [DecidablePred p] (A : Matrix ι ι K) (i j : ι) :
    (A * ind K p) i j = A i j * (if p j then 1 else 0) := by
  simp [ind, Matrix.mul_diagonal]

theorem rank_cut_le (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (A M B : Matrix ι ι K)
    (hA : ∀ i j, p i → ¬ p j → A i j = 0) (hB : ∀ i j, q j → ¬ q i → B i j = 0) :
    (ind K p * (A * M * B) * ind K q).rank ≤ (ind K p * M * ind K q).rank := by
  have h1 : ind K p * A = ind K p * A * ind K p := by
    ext i j
    rw [mul_ind_apply, ind_mul_apply]
    by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj, hA i j]
  have h2 : B * ind K q = ind K q * (B * ind K q) := by
    ext i j
    rw [ind_mul_apply, mul_ind_apply]
    by_cases hi : q i <;> by_cases hj : q j <;> simp [hi, hj, hB i j]
  have h3 : ind K p * (A * M * B) * ind K q =
      (ind K p * A) * (ind K p * M * ind K q) * (B * ind K q) := by
    calc ind K p * (A * M * B) * ind K q = (ind K p * A) * M * (B * ind K q) := by
          simp only [Matrix.mul_assoc]
      _ = (ind K p * A * ind K p) * M * (ind K q * (B * ind K q)) := by rw [← h1, ← h2]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h3]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem pm_apply (σ : Equiv.Perm ι) (i j : ι) :
    ((pm K σ : GL ι K) : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
  simp only [pm, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Equiv.Perm.inv_eq_iff_eq]

theorem rank_cut_pm (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (σ : Equiv.Perm ι) :
    (ind K p * ((pm K σ : GL ι K) : Matrix ι ι K) * ind K q).rank =
      (Finset.univ.filter fun j => q j ∧ p (σ j)).card := by
  have h : ind K p * ((pm K σ : GL ι K) : Matrix ι ι K) * ind K q =
      ((pm K σ : GL ι K) : Matrix ι ι K) *
        Matrix.diagonal fun j => if q j ∧ p (σ j) then (1 : K) else 0 := by
    ext i j
    rw [mul_ind_apply, ind_mul_apply, Matrix.mul_diagonal, pm_apply]
    by_cases hij : i = σ j
    · subst hij
      by_cases h1 : p (σ j) <;> by_cases h2 : q j <;> simp [h1, h2]
    · simp [hij]
  rw [h, Matrix.rank_mul_eq_right_of_isUnit_det, Matrix.rank_diagonal, Fintype.card_subtype]
  · congr 1
    ext j
    by_cases h1 : q j ∧ p (σ j) <;> simp [h1]
  · exact (Matrix.isUnit_iff_isUnit_det _).1 (pm K σ).isUnit

def cnt {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ : Equiv.Perm ι) (a a' : ℕ) : ℕ :=
  (Finset.univ.filter fun j => (b j : ℕ) < a ∧ a' ≤ (b' (σ j) : ℕ)).card

theorem cnt_le {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ τ : Equiv.Perm ι)
    (h : ∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K τ = β * pm K σ * α) (a a' : ℕ) :
    cnt b b' τ a a' ≤ cnt b b' σ a a' := by
  obtain ⟨β, hβ, α, hα, e⟩ := h
  have hM : ((pm K τ : GL ι K) : Matrix ι ι K) =
      (β : Matrix ι ι K) * ((pm K σ : GL ι K) : Matrix ι ι K) * (α : Matrix ι ι K) := by
    rw [e]; simp [Units.val_mul]
  have key := rank_cut_le (K := K) (fun i => a' ≤ (b' i : ℕ)) (fun j => (b j : ℕ) < a)
    (β : Matrix ι ι K) ((pm K σ : GL ι K) : Matrix ι ι K) (α : Matrix ι ι K)
    (fun i j hi hj => hβ.1 i j (by
      rw [Fin.lt_def]; exact lt_of_lt_of_le (not_le.mp hj) hi))
    (fun i j hj hi => hα.1 i j (by
      rw [Fin.lt_def]; exact lt_of_lt_of_le hj (not_lt.mp hi)))
  rw [← hM, rank_cut_pm, rank_cut_pm] at key
  exact key

theorem cnt_eq {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ τ : Equiv.Perm ι)
    (h : ∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K τ = β * pm K σ * α) (a a' : ℕ) :
    cnt b b' τ a a' = cnt b b' σ a a' := by
  refine le_antisymm (cnt_le (K := K) b b' σ τ h a a') (cnt_le (K := K) b b' τ σ ?_ a a')
  obtain ⟨β, hβ, α, hα, e⟩ := h
  refine ⟨β⁻¹, inv_mem hβ, α⁻¹, inv_mem hα, ?_⟩
  rw [e]; group

theorem cnt_diff {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ : Equiv.Perm ι)
    (c : Fin s) (c' : Fin s') :
    cnt b b' σ (c + 1) c' + cnt b b' σ c (c' + 1) =
      cnt b b' σ c c' + cnt b b' σ (c + 1) (c' + 1) +
        Fintype.card {i // b i = c ∧ b' (σ i) = c'} := by
  rw [Fintype.card_subtype]
  simp only [cnt, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.ext_iff]
  split_ifs <;> omega

theorem bruhatUniq : ReciprocityTheory.Ty.Fin.St.BruhatUniq := by
  intro K _ _ _ ι _ _ s s' b b' σ τ h c c'
  have h1 := cnt_diff b b' σ c c'
  have h2 := cnt_diff b b' τ c c'
  simp only [cnt_eq (K := K) b b' σ τ h] at h2
  omega

end GlobalTheory.CompanionTheory.BruhatInv
