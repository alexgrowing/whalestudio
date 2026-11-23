import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations

open CategoryTheory GlobalTheory.EtC

noncomputable section

namespace LateralTheory.EtaleFoundations.AcycPf

def cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨fun i => Fin.cases 0 (fun j => a.toOrderHom j) i, by
    intro i j h
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (by simp)
      | succ j => simpa using a.toOrderHom.monotone (Fin.succ_le_succ_iff.1 h)⟩

def v0 {N : ℕ} : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

@[simp] lemma cone_zero {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    (cone a).toOrderHom 0 = 0 := rfl
@[simp] lemma cone_succ {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (j : Fin (p + 1)) :
    (cone a).toOrderHom j.succ = a.toOrderHom j := rfl
@[simp] lemma vertex_zero_apply {N : ℕ} (j : Fin 1) : (v0 (N := N)).toOrderHom j = 0 := rfl

lemma δ0_cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 0 ≫ cone a = a := by
  ext j
  simp [SimplexCategory.δ]

lemma δsucc_cone {p N : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (i : Fin (p + 2)) :
    SimplexCategory.δ i.succ ≫ cone a = cone (SimplexCategory.δ i ≫ a) := by
  ext j
  induction j using Fin.cases with
  | zero => simp [SimplexCategory.δ]
  | succ j => simp [SimplexCategory.δ, Fin.succ_succAbove_succ]

lemma δ1_cone {N : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 1 ≫ cone a = v0 := by
  ext j
  fin_cases j
  simp [SimplexCategory.δ]

abbrev X {N : ℕ} (p r : ℕ) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) : Pr N →₀ ℤ :=
  Finsupp.single (⟨p, r, a, b⟩ : Pr N) 1

def Hg {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  X (z.1 + 1) z.2.1 (cone z.2.2.1) z.2.2.2 + if z.1 = 0 then X 0 (z.2.1 + 1) v0 (cone z.2.2.2) else 0

def H (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ Hg

lemma d_X {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d N (X p r a b) = Pr.d₁ (⟨p, r, a, b⟩ : Pr N) + (-1 : ℤ) ^ p • Pr.d₂ (⟨p, r, a, b⟩ : Pr N) := by
  simp [Pr.d, X]

lemma H_X {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    H N (X p r a b) = Hg (⟨p, r, a, b⟩ : Pr N) := by
  simp [H, X]

lemma Hg_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Hg (⟨0, r, a, b⟩ : Pr N) = X 1 r (cone a) b + X 0 (r + 1) v0 (cone b) := by
  simp [Hg]

lemma Hg_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Hg (⟨p + 1, r, a, b⟩ : Pr N) = X (p + 2) r (cone a) b := by
  simp [Hg]

lemma diffOne_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

lemma simplex_pair_second_face_of_vertex_eq_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

lemma simplex_pair_first_face_succ_alternating_sum {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X p r (SimplexCategory.δ i ≫ a) b := by
  simp [Pr.d₁, X]

lemma simplex_pair_second_face_succ_alternating_sum {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) = ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • X p r a (SimplexCategory.δ i ≫ b) := by
  simp [Pr.d₂, X]

lemma simplex_pair_first_face_cone_vertex_formula {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨1, r, cone a, b⟩ : Pr N) = X 0 r a b - X 0 r v0 b := by
  rw [simplex_pair_first_face_succ_alternating_sum, Fin.sum_univ_two]
  have h1 : SimplexCategory.δ (1 : Fin 2) ≫ cone a = v0 := δ1_cone a
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, δ0_cone, h1, neg_smul, sub_eq_add_neg]

lemma simplex_pair_first_face_cone_succ_formula {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 2, r, cone a, b⟩ : Pr N) = X (p + 1) r a b - ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • X (p + 1) r (cone (SimplexCategory.δ i ≫ a)) b := by
  rw [simplex_pair_first_face_succ_alternating_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ0_cone, δsucc_cone, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma simplex_pair_second_face_cone_succ_formula {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1 + 1, a, cone b⟩ : Pr N) = X p (r + 1) a b - ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) • X p (r + 1) a (cone (SimplexCategory.δ i ≫ b)) := by
  rw [simplex_pair_second_face_succ_alternating_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, δ0_cone, δsucc_cone, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma alt_const {N : ℕ} (p : ℕ) (Y : Pr N →₀ ℤ) :
    ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (if p = 0 then Y else 0) = 0 := by
  cases p with
  | zero => simp [Fin.sum_univ_two]
  | succ p => simp

lemma key {N : ℕ} (z : Pr N) (hz : z.1 + z.2.1 ≠ 0) :
    Pr.d N (H N (Finsupp.single z 1)) + H N (Pr.d N (Finsupp.single z 1)) = Finsupp.single z 1 := by
  obtain ⟨p, r, a, b⟩ := z
  change Pr.d N (H N (X p r a b)) + H N (Pr.d N (X p r a b)) = X p r a b
  cases p with
  | zero =>
    cases r with
    | zero => simp at hz
    | succ r =>
      rw [H_X, Hg_zero, map_add, d_X, d_X, d_X, simplex_pair_first_face_cone_vertex_formula, diffOne_zero, diffOne_zero, simplex_pair_second_face_cone_succ_formula, simplex_pair_second_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum]
      simp only [map_add, map_sub, map_sum, map_zsmul, H_X, Hg_zero, smul_add, Finset.sum_add_distrib, zero_add,
        pow_zero, pow_one, one_smul, neg_smul, map_zero]
      abel
  | succ p =>
    cases r with
    | zero =>
      rw [H_X, Hg_succ, d_X, d_X, simplex_pair_first_face_cone_succ_formula, simplex_pair_first_face_succ_alternating_sum, simplex_pair_second_face_of_vertex_eq_zero, simplex_pair_second_face_of_vertex_eq_zero]
      simp only [map_add, map_sub, map_sum, map_zsmul, H_X, smul_zero, add_zero, map_zero]
      simp only [Hg, smul_add, Finset.sum_add_distrib, alt_const, add_zero]
      abel
    | succ r =>
      rw [H_X, Hg_succ, d_X, d_X, simplex_pair_first_face_cone_succ_formula, simplex_pair_first_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum, simplex_pair_second_face_succ_alternating_sum]
      simp only [map_add, map_sub, map_sum, map_zsmul, H_X, Hg_succ, map_zero]
      simp only [Hg, smul_add, Finset.sum_add_distrib, alt_const, add_zero]
      have e : (-1 : ℤ) ^ (p + 2) = -(-1) ^ (p + 1) := by ring
      rw [e, neg_smul]
      abel

lemma deg_H {N k : ℕ} {c : Pr N →₀ ℤ} (hdeg : Pr.Deg (k + 1) c) : Pr.Deg (k + 2) (H N c) := by
  intro z hz
  have e : H N c = ∑ y ∈ c.support, c y • Hg y := by
    simp [H, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [e] at hz
  obtain ⟨y, hy, hz2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have hz3 := Finsupp.support_smul hz2
  have hy' := hdeg y hy
  obtain ⟨p, r, a, b⟩ := y
  simp only [Hg] at hz3
  rcases Finset.mem_union.1 (Finsupp.support_add hz3) with h | h
  · have := Finsupp.support_single_subset h
    rw [Finset.mem_singleton] at this
    subst this
    change p + r = k + 1 at hy'
    change p + 1 + r = k + 2
    omega
  · split_ifs at h with hp
    · have := Finsupp.support_single_subset h
      rw [Finset.mem_singleton] at this
      subst this
      change p + r = k + 1 at hy'
      change 0 + (r + 1) = k + 2
      omega
    · simp at h

end LateralTheory.EtaleFoundations.AcycPf

open LateralTheory.EtaleFoundations.AcycPf in

theorem LateralTheory.EtaleFoundations.SteenPf.leaf_acyc_of : LateralTheory.EtaleFoundations.SteenPf.leaf_acyc := by
  intro N k c hdeg hcyc
  refine ⟨H N c, deg_H hdeg, ?_⟩
  have h : ∀ y ∈ c.support, Pr.d N (H N (Finsupp.single y (c y))) + H N (Pr.d N (Finsupp.single y (c y))) =
      Finsupp.single y (c y) := by
    intro y hy
    have hy' := hdeg y hy
    rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← smul_add, key y (by omega)]
  have e : Pr.d N (H N c) + H N (Pr.d N c) = c := by
    conv_rhs => rw [← Finsupp.sum_single c]
    conv_lhs => rw [← Finsupp.sum_single c]
    simp only [Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl h
  rw [hcyc, map_zero, add_zero] at e
  exact e

end
