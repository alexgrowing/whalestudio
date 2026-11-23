import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace PositivityTheory.HtPt.Gf

theorem minor_mul_upper {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g U : Matrix (Fin N) (Fin N) B)
    (J : Fin i → Fin N) (hU : ∀ a b, b < a → U a b = 0) :
    ((g * U).submatrix J (Fin.castLE hi)).det =
      (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l) := by
  have h : (g * U).submatrix J (Fin.castLE hi) =
      g.submatrix J (Fin.castLE hi) * U.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin i)).map (Fin.castLEEmb hi))) ?_,
      Finset.sum_map]
    · rfl
    · intro k _ hk
      have hki : i ≤ (k : ℕ) := by
        by_contra hlt
        push_neg at hlt
        exact hk (Finset.mem_map.2 ⟨⟨k, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have hlt : Fin.castLE hi b < k := by
        rw [Fin.lt_def, Fin.coe_castLE]
        omega
      rw [hU k (Fin.castLE hi b) hlt, mul_zero]
  have hT : (U.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
    intro a b hab
    have hab' : Fin.castLE hi b < Fin.castLE hi a := by
      rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact hab
    exact hU _ _ hab'
  rw [h, Matrix.det_mul, Matrix.det_of_upperTriangular hT]
  rfl

private theorem cb_lemma {B : Type} [CommRing B] {i N : ℕ} (A : Matrix (Fin i) (Fin N) B)
    (C : Matrix (Fin N) (Fin i) B) :
    (A * C).det = ∑ p : Fin i → Fin N, (∏ a, A a (p a)) * (C.submatrix p id).det := by
  have key : ∀ p : Fin i → Fin N, (C.submatrix p id).det =
      ∑ σ : Equiv.Perm (Fin i), Equiv.Perm.sign σ • ∏ a, C (p a) (σ a) := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  simp_rw [key]
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_smul_comm]

private theorem matAct_of_span_residue_spans {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g : Matrix (Fin N) (Fin N) B)
    (hg : IsUnit g.det) :
    Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : g⁻¹.submatrix (Fin.castLE hi) id * g.submatrix id (Fin.castLE hi) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul g hg]
    exact Matrix.submatrix_one _ (Fin.castLE_injective hi)
  have h2 := cb_lemma (g⁻¹.submatrix (Fin.castLE hi) id) (g.submatrix id (Fin.castLE hi))
  rw [h1, Matrix.det_one] at h2
  rw [h2]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, rfl⟩)

theorem lead_minor : ∀ (B : Type) [CommRing B] (N i : ℕ) (hi : i ≤ N), (∀ (g U : Matrix (Fin N) (Fin N) B) (J : Fin i → Fin N), (∀ a b, b < a → U a b = 0) → ((g * U).submatrix J (Fin.castLE hi)).det = (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l)) ∧ ∀ g : Matrix (Fin N) (Fin N) B, IsUnit g.det → Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  intro B _ N i hi
  exact ⟨fun g U J hU => minor_mul_upper hi g U J hU, fun g hg => matAct_of_span_residue_spans hi g hg⟩

theorem abel_nat (lam x : ℕ → ℝ) (n : ℕ) (hl : ∀ i, i + 1 ≤ n → lam (i + 1) ≤ lam i)
    (hx : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x l) :
    lam n * ∑ l ∈ Finset.range (n + 1), x l ≤ ∑ l ∈ Finset.range (n + 1), lam l * x l := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hl j (by omega)) (fun j hj => hx j (by omega))
    have hs := hx (n + 1) le_rfl
    have hln := hl n le_rfl
    rw [Finset.sum_range_succ x (n + 1), Finset.sum_range_succ (fun l => lam l * x l) (n + 1)]
    nlinarith [mul_nonneg (sub_nonneg.2 hln) hs]

theorem abel_sum : ∀ (N : ℕ) (lam x : Fin N → ℝ), (∀ i j, i ≤ j → lam j ≤ lam i) → (∀ i : ℕ, i ≤ N → 0 ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), x l) → ∑ l, x l = 0 → 0 ≤ ∑ l, lam l * x l := by
  intro N lam x hl hx hsum
  cases N with
  | zero => simp
  | succ n =>
    obtain ⟨x', hx'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = x l :=
      ⟨fun k => if h : k < n + 1 then x ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    obtain ⟨lam', hlam'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = lam l :=
      ⟨fun k => if h : k < n + 1 then lam ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    have hsx : ∀ i, i ≤ n + 1 → ∑ l ∈ Finset.range i, x' l =
        ∑ l ∈ Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < i), x l := by
      intro i hi
      have e : ∀ l : Fin (n + 1), (if (l : ℕ) < i then x l else 0) =
          (fun k => if k < i then x' k else 0) (l : ℕ) := by
        intro l
        simp only [hx']
      rw [Finset.sum_filter, Finset.sum_congr rfl (fun l _ => e l),
        Fin.sum_univ_eq_sum_range (fun k => if k < i then x' k else 0), ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    have htot : ∑ l ∈ Finset.range (n + 1), x' l = 0 := by
      rw [← Fin.sum_univ_eq_sum_range x' (n + 1)]
      simp only [hx']
      exact hsum
    have hprod : ∑ l ∈ Finset.range (n + 1), lam' l * x' l = ∑ l, lam l * x l := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => lam' k * x' k) (n + 1)]
      simp only [hx', hlam']
    have hl' : ∀ i, i + 1 ≤ n → lam' (i + 1) ≤ lam' i := by
      intro i hi
      have h1 := hlam' ⟨i + 1, by omega⟩
      have h2 := hlam' ⟨i, by omega⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hl _ _ (Fin.mk_le_mk.2 (by omega))
    have hx'' : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x' l := by
      intro i hi
      rw [hsx i (by omega)]
      exact hx i (by omega)
    have key := abel_nat lam' x' n hl' hx''
    rw [htot, hprod, mul_zero] at key
    exact key

end PositivityTheory.HtPt.Gf
