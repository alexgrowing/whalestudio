import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwPf

abbrev sb {n : ℕ} (j l : ℕ) (h : j + l ≤ n) : SimplexCategory.mk l ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval j l h

@[simp] lemma sb_apply {n : ℕ} (j l : ℕ) (h : j + l ≤ n) (i : Fin (l + 1)) :
    (((sb j l h).toOrderHom i : Fin (n + 1)) : ℕ) = i + j := rfl

lemma m_last (p r : ℕ) (h1 : 0 + (p + 1) ≤ p + r + 1) (h2 : 0 + p ≤ p + r + 1) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫ sb 0 (p + 1) h1 = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_zero (p r : ℕ) (h1 : p + (r + 1) ≤ p + r + 1) (h2 : (p + 1) + r ≤ p + r + 1) :
    SimplexCategory.δ 0 ≫ sb p (r + 1) h1 = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_lo (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + (p + 1) ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k, by omega⟩ : Fin (p + 2)) ≫ sb 0 (p + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_within_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : (k : ℕ) ≤ p) (h1 : p + r ≤ p + r)
    (h2 : (p + 1) + r ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = sb (p + 1) r h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma m_hi (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : 0 + p ≤ p + r)
    (h2 : 0 + p ≤ p + r + 1) :
    sb 0 p h1 ≫ SimplexCategory.δ k = sb 0 p h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

lemma simplex_subinterval_back_comp_face_above_front (p r : ℕ) (k : Fin (p + r + 2)) (hk : p < (k : ℕ)) (h1 : p + r ≤ p + r)
    (h2 : p + (r + 1) ≤ p + r + 1) :
    sb p r h1 ≫ SimplexCategory.δ k = SimplexCategory.δ (⟨k - p, by omega⟩ : Fin (r + 2)) ≫ sb p (r + 1) h2 := by
  ext i : 3
  apply Fin.ext
  simp [SimplexCategory.δ, Fin.succAbove, Fin.lt_def, sb_apply]
  try split_ifs
  all_goals (try simp_all [Fin.lt_def, sb_apply])
  all_goals omega

def T (n p r : ℕ) (h : p + r ≤ n) : Pr n := ⟨p, r, sb 0 p (by omega), sb p r h⟩

noncomputable def S (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Finsupp.single (T n x.1 x.2 h) 1 else 0

noncomputable def g1 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then Pr.d₁ (T n x.1 x.2 h) else 0

noncomputable def g2 (n : ℕ) (x : ℕ × ℕ) : Pr n →₀ ℤ :=
  if h : x.1 + x.2 ≤ n then (-1 : ℤ) ^ x.1 • Pr.d₂ (T n x.1 x.2 h) else 0

lemma aw_eq (n : ℕ) : Pr.aw n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, S n x := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range (fun k => S n (k, n - k))]
  unfold Pr.aw
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.isLt
  simp only [S]
  rw [dif_pos (by omega)]
  rfl

lemma bd_sum {N : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Pr N →₀ ℤ) :
    Pr.bd (∑ x ∈ s, g x) = ∑ x ∈ s, Pr.bd (g x) := by
  unfold Pr.bd
  simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_comm

lemma d_S (n : ℕ) (x : ℕ × ℕ) : Pr.d n (S n x) = g1 n x + g2 n x := by
  unfold S g1 g2
  split_ifs with h
  · simp only [Pr.d, Finsupp.linearCombination_single, one_smul]
    rfl
  · simp

lemma split_sum {M : Type*} [AddCommMonoid M] (p r : ℕ) (f : Fin (p + r + 2) → M) :
    ∑ k, f k = ∑ i : Fin (p + 1), f ⟨i, by omega⟩ + ∑ j : Fin (r + 1), f ⟨p + 1 + j, by omega⟩ := by
  rw [← (finCongr (by omega : (p + 1) + (r + 1) = p + r + 2)).sum_comp, Fin.sum_univ_add]
  rfl

lemma bd_single (n : ℕ) (z : Pr n) : Pr.bd (Finsupp.single z 1) =
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • Finsupp.single
      (⟨z.1, z.2.1, z.2.2.1 ≫ SimplexCategory.δ k, z.2.2.2 ≫ SimplexCategory.δ k⟩ : Pr (n + 1)) 1 := by
  unfold Pr.bd
  simp [Pr.push]

lemma key (p r : ℕ) :
    Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) + (-1 : ℤ) ^ p • Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) =
      Pr.bd (Finsupp.single (T (p + r) p r le_rfl) 1) := by
  have e1 : Pr.d₁ (T (p + r + 1) (p + 1) r (by omega)) = ∑ i : Fin (p + 2),
      Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (i : ℕ)) := rfl
  have e2 : Pr.d₂ (T (p + r + 1) p (r + 1) (by omega)) = ∑ j : Fin (r + 2),
      Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ (j : ℕ)) := rfl
  rw [e1, e2, bd_single, split_sum, Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1)]
  have hlo : ∀ i : Fin (p + 1),
      (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      Finsupp.single (⟨p, r, SimplexCategory.δ i.castSucc ≫ sb 0 (p + 1) (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.castSucc i : Fin (p + 2)) : ℕ)) := by
    intro i
    have hi := i.isLt
    simp only [T]
    rw [m_lo p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega), simplex_subinterval_back_comp_face_within_front p r _ (by show (i : ℕ) ≤ p; omega) _ (by omega),
      Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  have hhi : ∀ j : Fin (r + 1),
      (-1 : ℤ) ^ (p + 1 + (j : ℕ)) • Finsupp.single (⟨(T (p + r) p r le_rfl).1, (T (p + r) p r le_rfl).2.1,
        (T (p + r) p r le_rfl).2.2.1 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2)),
        (T (p + r) p r le_rfl).2.2.2 ≫ SimplexCategory.δ (⟨p + 1 + j, by omega⟩ : Fin (p + r + 2))⟩ : Pr (p + r + 1)) 1 =
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), SimplexCategory.δ j.succ ≫ sb p (r + 1) (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.succ j : Fin (r + 2)) : ℕ)) := by
    intro j
    have hj := j.isLt
    simp only [T]
    rw [m_hi p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega), simplex_subinterval_back_comp_face_above_front p r _ (by show p < p + 1 + (j : ℕ); omega) _ (by omega),
      Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one]
    have hf : (⟨p + 1 + (j : ℕ) - p, by omega⟩ : Fin (r + 2)) = j.succ := by
      ext; simp; omega
    rw [hf, Fin.val_succ]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun i _ => hlo i), Finset.sum_congr rfl (fun j _ => hhi j), ← Finset.smul_sum,
    m_last p r (by omega) (by omega), m_zero p r (by omega) (by omega), smul_add]
  have hc : Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ)) +
      (-1 : ℤ) ^ p • Finsupp.single (⟨p, r, sb 0 p (by omega), sb (p + 1) r (by omega)⟩ : Pr (p + r + 1))
        ((-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ)) = 0 := by
    rw [Finsupp.smul_single, ← Finsupp.single_add]
    simp [pow_succ]
  apply eq_of_sub_eq_zero
  rw [← hc]
  abel

theorem leaf_aw_of : LateralTheory.EtaleFoundations.SteenPf.leaf_aw := by
  intro N
  rw [aw_eq, aw_eq, map_sum, bd_sum]
  simp only [d_S]
  rw [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  have z1 : g1 (N + 1) (0, N + 1) = 0 := by
    unfold g1; rw [dif_pos (by simp)]; rfl
  have z2 : g2 (N + 1) (N + 1, 0) = 0 := by
    unfold g2; rw [dif_pos (by simp)]
    show (-1 : ℤ) ^ (N + 1) • (0 : Pr (N + 1) →₀ ℤ) = 0
    exact smul_zero _
  rw [z1, z2, zero_add, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨p, r⟩ := x
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  simp only at hx
  subst hx
  unfold g1 g2 S
  rw [dif_pos (by simp; omega), dif_pos (by simp; omega), dif_pos (by simp)]
  exact key p r

end LateralTheory.EtaleFoundations.AwPf
