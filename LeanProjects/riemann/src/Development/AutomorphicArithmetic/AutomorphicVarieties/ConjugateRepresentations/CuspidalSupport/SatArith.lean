import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem es_zero (A : Multiset ℂ) : A.esymm 0 = 1 := by simp [Multiset.esymm]

private theorem es_cons (a : ℂ) (A : Multiset ℂ) (k : ℕ) :
    (a ::ₘ A).esymm (k + 1) = A.esymm (k + 1) + a * A.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

private theorem es_big (A : Multiset ℂ) {k : ℕ} (h : A.card < k) : A.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

private theorem es_add (A C : Multiset ℂ) (j : ℕ) :
    (A + C).esymm j = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j, A.esymm p.1 * C.esymm p.2 := by
  induction A using Multiset.induction_on generalizing j with
  | empty =>
    rw [Finset.sum_eq_single (0, j)]
    · simp [es_zero]
    · rintro ⟨i, k⟩ hp hne
      have : 0 < i := by
        rcases Nat.eq_zero_or_pos i with rfl | h
        · simp at hp; simp [hp] at hne
        · exact h
      rw [es_big 0 (by simpa using this), zero_mul]
    · simp
  | cons a A ih =>
    cases j with
    | zero => simp [es_zero]
    | succ j =>
      rw [Multiset.cons_add, es_cons, ih, ih, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
      simp only [es_cons, es_zero, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]

private theorem es_add_fin (A C : Multiset ℂ) {r s : ℕ} (hA : A.card = r) (hC : C.card = s) (j : ℕ) :
    (A + C).esymm j =
      ∑ p : Fin (r + 1) × Fin (s + 1), if (p.1 : ℕ) + p.2 = j then A.esymm p.1 * C.esymm p.2 else 0 := by
  rw [es_add, ← Finset.sum_filter]
  symm
  refine Finset.sum_of_injOn (fun p => ((p.1 : ℕ), (p.2 : ℕ))) ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨a, b⟩ - ⟨c, d⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · intro p hp
    simpa using hp
  · rintro ⟨i, k⟩ hp hn
    by_cases hi : r < i
    · rw [es_big A (hA ▸ hi), zero_mul]
    by_cases hk : s < k
    · rw [es_big C (hC ▸ hk), mul_zero]
    exact absurd ⟨(⟨i, by omega⟩, ⟨k, by omega⟩), by simpa using hp, rfl⟩ hn

private theorem es_scale (A : Multiset ℂˣ) (c : ℂˣ) (k : ℕ) :
    ((A.map (· * c)).map fun b : ℂˣ => (b : ℂ)).esymm k = (c : ℂ) ^ k * (A.map fun b : ℂˣ => (b : ℂ)).esymm k := by
  rw [← smul_eq_mul, Multiset.pow_smul_esymm]
  simp [Multiset.map_map, mul_comm]

theorem UpperTheory.V.Cj.S.satArith :
    UpperTheory.V.Cj.S.SatArith := by
  intro q r s hq B B₁ B₂ hB h₁ h₂ h α β hα hβ
  refine eq_of_satEig_eq hq hB (by simp [h₁, h₂]) fun j hj => ?_
  rw [← h j hj, satEig, Multiset.map_add, es_add_fin (r := r) (s := s) _ _ (by simpa using h₁) (by simpa using h₂),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold coef
  split_ifs with hp
  swap
  · simp
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hk : (p.2 : ℕ) ≤ s := Nat.lt_succ_iff.1 p.2.2
  have key : (q : ℂ) ^ ((p.1 : ℕ) * (s - p.2)) * (q : ℂ) ^ ((((p.1 : ℕ) : ℂ) * ((r : ℂ) - (p.1 : ℕ))) / 2) *
      (q : ℂ) ^ ((((p.2 : ℕ) : ℂ) * ((s : ℂ) - (p.2 : ℕ))) / 2) =
      (q : ℂ) ^ (((j : ℂ) * (((r + s : ℕ) : ℂ) - j)) / 2) * (α : ℂ) ^ (p.1 : ℕ) * (β : ℂ) ^ (p.2 : ℕ) := by
    rw [hα, hβ, ← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq',
      ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq', ← hp]
    congr 1
    push_cast [hk]
    ring
  rw [es_scale, es_scale, satEig, satEig]
  linear_combination ((B₁.map fun b : ℂˣ => (b : ℂ)).esymm p.1 * (B₂.map fun b : ℂˣ => (b : ℂ)).esymm p.2) * key
