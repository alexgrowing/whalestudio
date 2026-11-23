import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmSecond

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree

variable {k : Type} [CommRing k]

section General

variable {σ : Type} [Fintype σ]

theorem so_def (c : σ → σ → k) (P : MvPolynomial σ k) :
    secondOrder k c P = ∑ l, ∑ l', C (c l l') * pderiv l (pderiv l' P) := rfl

theorem so_zero (c : σ → σ → k) : secondOrder k c (0 : MvPolynomial σ k) = 0 := by
  simp [so_def]

theorem so_add (c : σ → σ → k) (P Q : MvPolynomial σ k) :
    secondOrder k c (P + Q) = secondOrder k c P + secondOrder k c Q := by
  simp only [so_def, map_add, mul_add, Finset.sum_add_distrib]

theorem so_smul (c : σ → σ → k) (r : k) (P : MvPolynomial σ k) :
    secondOrder k c (r • P) = r • secondOrder k c P := by
  first
  | (simp only [so_def, MvPolynomial.smul_eq_C_mul, Finset.mul_sum, Derivation.leibniz, smul_eq_mul,
      pderiv_C, mul_zero, add_zero]
     refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
     ring)
  | simp [so_def, Finset.smul_sum, mul_smul_comm]

private theorem mvPolynomial_pderiv_comm (a b : σ) (P : MvPolynomial σ k) :
    pderiv a (pderiv b P) = pderiv b (pderiv a P) := by
  classical
  induction P using MvPolynomial.induction_on
  · simp
  · simp [*]
  · rename_i p m hp
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hp, pderiv_X]
    by_cases ha : a = m <;> by_cases hb : b = m <;> simp [Pi.single_apply, ha, hb] <;> ring

theorem pd4 (P : MvPolynomial σ k) (a b c d : σ) :
    pderiv a (pderiv b (pderiv c (pderiv d P))) = pderiv c (pderiv d (pderiv a (pderiv b P))) := by
  rw [mvPolynomial_pderiv_comm b c, mvPolynomial_pderiv_comm a c, mvPolynomial_pderiv_comm b d, mvPolynomial_pderiv_comm a d]

private theorem sum4_lemma {M : Type} [AddCommMonoid M] (f : σ → σ → σ → σ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem so_comm (c1 c2 : σ → σ → k) (P : MvPolynomial σ k) :
    secondOrder k c1 (secondOrder k c2 P) = secondOrder k c2 (secondOrder k c1 P) := by
  simp only [so_def, map_sum, Finset.mul_sum, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero,
    add_zero]
  rw [sum4_lemma]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ =>
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [pd4]
  ring

theorem totalDegree_pderiv_le (i : σ) (Q : MvPolynomial σ k) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree - 1 := by
  classical
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    have h1 := MvPolynomial.le_totalDegree hs
    have h2 : s = (s - Finsupp.single i 1) + Finsupp.single i 1 :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))).symm
    have h3 : (s.sum fun _ e => e) = ((s - Finsupp.single i 1).sum fun _ e => e) + 1 := by
      conv_lhs => rw [h2]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have h4 : ((s - Finsupp.single i 1).sum fun _ => id) = ((s - Finsupp.single i 1).sum fun _ e => e) := rfl
    have h5 : (s.sum fun _ => id) = (s.sum fun _ e => e) := rfl
    omega

theorem pderiv_eq_zero_of_deg (i : σ) (Q : MvPolynomial σ k) (h : Q.totalDegree = 0) : pderiv i Q = 0 := by
  first
  | (rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h; rw [h, pderiv_C])
  | (have h' := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).1 h; rw [h', pderiv_C])

theorem totalDegree_so_le (c : σ → σ → k) (Q : MvPolynomial σ k) :
    (secondOrder k c Q).totalDegree ≤ Q.totalDegree - 2 := by
  rw [so_def]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l' _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  have h1 := totalDegree_pderiv_le l (pderiv l' Q)
  have h2 := totalDegree_pderiv_le l' Q
  omega

theorem so_eq_zero_of_le_one (c : σ → σ → k) (Q : MvPolynomial σ k) (h : Q.totalDegree ≤ 1) :
    secondOrder k c Q = 0 := by
  rw [so_def]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun l' _ => ?_
  have h1 := totalDegree_pderiv_le l' Q
  rw [pderiv_eq_zero_of_deg l (pderiv l' Q) (by omega), mul_zero]

theorem so_iter_eq_zero (c : σ → σ → k) :
    ∀ (i : ℕ) (Q : MvPolynomial σ k), Q.totalDegree < i → (secondOrder k c)^[i] Q = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | i + 1, Q, h => by
    rw [Function.iterate_succ_apply]
    by_cases h1 : Q.totalDegree ≤ 1
    · rw [so_eq_zero_of_le_one c Q h1]
      exact Function.iterate_fixed (so_zero c) i
    · apply so_iter_eq_zero c i
      have := totalDegree_so_le c Q
      omega

theorem so_iter_deg_le (c : σ → σ → k) :
    ∀ (i : ℕ) (Q : MvPolynomial σ k), ((secondOrder k c)^[i] Q).totalDegree ≤ Q.totalDegree
  | 0, _ => le_rfl
  | i + 1, Q => by
    rw [Function.iterate_succ_apply]
    refine (so_iter_deg_le c i _).trans ?_
    have := totalDegree_so_le c Q
    omega

end General

section Columns

variable {ι : Type} [Fintype ι] {n : ℕ}

abbrev colE (b : Fin n) : MvPolynomial ι k →ₐ[k] MvPolynomial (ι × Fin n) k := rename fun l => (l, b)

def cB (c : ι → ι → k) (b : Fin n) : ι × Fin n → ι × Fin n → k :=
  fun p q => if p.2 = b ∧ q.2 = b then c p.1 q.1 else 0

theorem pderiv_colE (b : Fin n) (l : ι) (Q : MvPolynomial ι k) :
    pderiv (l, b) (colE b Q) = colE b (pderiv l Q) := by
  classical
  first
  | exact pderiv_rename (f := fun l => (l, b)) (fun x y h => by simpa using h) l Q
  | simpa using pderiv_rename (f := fun l : ι => (l, b)) (fun x y h => by simpa using h) l Q

private theorem pderiv_colE_eq_zero_of_ne (a b : Fin n) (hab : a ≠ b) (l : ι) (P : MvPolynomial ι k) :
    pderiv (l, b) (colE a P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on
  · simp
  · simp [*]
  · rename_i p m hp
    simp [hp, pderiv_X, Pi.single_apply, hab]

theorem pderiv_prod_colE (b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) (Q : Fin n → MvPolynomial ι k)
    (l : ι) : pderiv (l, b) (∏ b' ∈ s, colE b' (Q b')) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih (fun h => hb (Finset.mem_insert_of_mem h)),
      pderiv_colE_eq_zero_of_ne a b (by rintro rfl; exact hb (Finset.mem_insert_self _ _)) l (Q a)]
    simp

theorem so_colB (c : ι → ι → k) (b : Fin n) (Q : MvPolynomial ι k) (R : MvPolynomial (ι × Fin n) k)
    (hR : ∀ l : ι, pderiv (l, b) R = 0) :
    secondOrder k (cB c b) (colE b Q * R) = colE b (secondOrder k c Q) * R := by
  classical
  have hd : ∀ l l' : ι, pderiv (l, b) (pderiv (l', b) (colE b Q * R)) =
      colE b (pderiv l (pderiv l' Q)) * R := by
    intro l l'
    rw [Derivation.leibniz, hR, smul_zero, zero_add, smul_eq_mul, pderiv_colE,
      Derivation.leibniz, hR, smul_zero, add_zero, smul_eq_mul, pderiv_colE, mul_comm]
  have key : ∀ p q : ι × Fin n, C (cB c b p q) * pderiv p (pderiv q (colE b Q * R)) =
      if p.2 = b ∧ q.2 = b then C (c p.1 q.1) * (colE b (pderiv p.1 (pderiv q.1 Q)) * R) else 0 := by
    rintro ⟨l, y⟩ ⟨l', y'⟩
    simp only [cB]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [hd]
    · simp
  rw [so_def, so_def]
  simp only [key, map_sum, Finset.sum_mul, map_mul, MvPolynomial.rename_C]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single b]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [mul_assoc]
    · intro y _ hy
      simp [hy]
    · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem so_colB_iter (c : ι → ι → k) (b : Fin n) (R : MvPolynomial (ι × Fin n) k)
    (hR : ∀ l : ι, pderiv (l, b) R = 0) :
    ∀ (i : ℕ) (Q : MvPolynomial ι k),
      (secondOrder k (cB c b))^[i] (colE b Q * R) = colE b ((secondOrder k c)^[i] Q) * R
  | 0, _ => rfl
  | i + 1, Q => by
    rw [Function.iterate_succ_apply, so_colB c b Q R hR, so_colB_iter c b R hR i,
      ← Function.iterate_succ_apply]

end Columns

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
