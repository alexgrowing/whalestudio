import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertHeis

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

section Entries

variable {u : GU σ (N + 2)}

private theorem mat_apply_eq_one_apply_of_mem_radQ_of_blk_le (hu : u ∈ radQ σ N) (i j : Fin (N + 2)) (h : blk N j ≤ blk N i) :
    mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j :=
  hu i j h

theorem rad_zero_zero (hu : u ∈ radQ σ N) : mat u 0 0 = 1 := by
  rw [mat_apply_eq_one_apply_of_mem_radQ_of_blk_le hu 0 0 le_rfl, Matrix.one_apply_eq]

theorem rad_mid_zero (hu : u ∈ radQ σ N) (i : Fin N) : mat u (mid i) 0 = 0 := by
  rw [mat_apply_eq_one_apply_of_mem_radQ_of_blk_le hu _ _ (by simp [blk_zero]), Matrix.one_apply_ne (mid_ne_zero i)]

theorem rad_mid_mid (hu : u ∈ radQ σ N) (i j : Fin N) :
    mat u (mid i) (mid j) = (1 : Matrix (Fin N) (Fin N) L) i j := by
  rw [mat_apply_eq_one_apply_of_mem_radQ_of_blk_le hu _ _ (by simp [blk_mid])]
  simp only [Matrix.one_apply, mid_injective.eq_iff]

theorem rad_last_zero (hu : u ∈ radQ σ N) : mat u (Fin.last (N + 1)) 0 = 0 := by
  rw [mat_apply_eq_one_apply_of_mem_radQ_of_blk_le hu _ _ (by simp [blk_zero]), Matrix.one_apply_ne last_ne_zero]

theorem rad_last_mid (hu : u ∈ radQ σ N) (j : Fin N) : mat u (Fin.last (N + 1)) (mid j) = 0 := by
  rw [mat_apply_eq_one_apply_of_mem_radQ_of_blk_le hu _ _ (by simp [blk_mid, blk_last]), Matrix.one_apply_ne (mid_ne_last j).symm]

theorem rad_last_last (hu : u ∈ radQ σ N) : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by
  rw [mat_apply_eq_one_apply_of_mem_radQ_of_blk_le hu _ _ le_rfl, Matrix.one_apply_eq]

end Entries

private theorem mat_mul_eq_ite_of_hasMult (u u' : GU σ (N + 2)) (i j : Fin (N + 2)) :
    mat (u * u') i j = mat u i 0 * mat u' 0 j + ∑ m, mat u i (mid m) * mat u' (mid m) j +
      mat u i (Fin.last (N + 1)) * mat u' (Fin.last (N + 1)) j := by
  show (mat u * mat u') i j = _
  rw [Matrix.mul_apply, sum_idx]

theorem rowOf_mul {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u * u') = rowOf u + rowOf u' := by
  funext j
  show mat (u * u') 0 (mid j) = mat u 0 (mid j) + mat u' 0 (mid j)
  rw [mat_mul_eq_ite_of_hasMult, rad_zero_zero hu, rad_last_mid hu' j]
  simp only [rad_mid_mid hu', Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, one_mul, add_zero]
  ring

theorem colOf_mul {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    colOf (u * u') = colOf u + colOf u' := by
  funext i
  show mat (u * u') (mid i) (Fin.last (N + 1)) =
    mat u (mid i) (Fin.last (N + 1)) + mat u' (mid i) (Fin.last (N + 1))
  rw [mat_mul_eq_ite_of_hasMult, rad_mid_zero hu i, rad_last_last hu']
  simp only [rad_mid_mid hu, Matrix.one_apply, ite_mul, one_mul, zero_mul, zero_add, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem cornerOf_mul {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u' := by
  show mat (u * u') 0 (Fin.last (N + 1)) =
    mat u 0 (Fin.last (N + 1)) + mat u' 0 (Fin.last (N + 1)) + rowOf u ⬝ᵥ colOf u'
  rw [mat_mul_eq_ite_of_hasMult, rad_zero_zero hu, rad_last_last hu', dotProduct]
  simp only [rowOf, colOf, one_mul, mul_one]
  ring

theorem rowOf_one : rowOf (1 : GU σ (N + 2)) = 0 := by
  funext j
  show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 (mid j) = 0
  exact Matrix.one_apply_ne (mid_ne_zero j).symm

theorem colOf_one : colOf (1 : GU σ (N + 2)) = 0 := by
  funext i
  show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) (Fin.last (N + 1)) = 0
  exact Matrix.one_apply_ne (mid_ne_last i)

theorem cornerOf_one : cornerOf (1 : GU σ (N + 2)) = 0 := by
  show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 (Fin.last (N + 1)) = 0
  exact Matrix.one_apply_ne (fun h => last_ne_zero h.symm)

private theorem antiJ_apply_eq_ite_rev {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if j = i.rev then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  show (if (i : ℕ) + j + 1 = n then (1 : L) else 0) = _
  by_cases h : j = i.rev
  · rw [if_pos h, if_pos]
    subst h
    rw [Fin.val_rev]
    omega
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    ext
    rw [Fin.val_rev]
    omega

private theorem antiJ_mul_apply_eq_apply_rev_left {n : ℕ} (X : Matrix (Fin n) (Fin n) L) (a c : Fin n) :
    (antiJ L n * X) a c = X a.rev c := by
  rw [Matrix.mul_apply]
  simp only [antiJ_apply_eq_ite_rev, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem mul_antiJ_apply_eq_apply_rev_right {n : ℕ} (X : Matrix (Fin n) (Fin n) L) (c b : Fin n) :
    (X * antiJ L n) c b = X c b.rev := by
  rw [Matrix.mul_apply]
  have e : ∀ d : Fin n, (b = d.rev) = (d = b.rev) := fun d =>
    propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp only [antiJ_apply_eq_ite_rev, e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem antiJ_mul_antiJ_eq_one {n : ℕ} : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul_apply_eq_apply_rev_left, antiJ_apply_eq_ite_rev, Fin.rev_rev]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg (Ne.symm h), Matrix.one_apply_ne h]

private theorem mat_inv_apply_eq_sigma_mat_rev {n : ℕ} (g : GU σ n) (a b : Fin n) :
    mat g⁻¹ a b = σ (mat g b.rev a.rev) := by
  have hU : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have hinv : mat g * mat g⁻¹ = 1 := by
    show mat (g * g⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have key : mat g⁻¹ = antiJ L n * cT σ (mat g) * antiJ L n := by
    calc mat g⁻¹ = antiJ L n * antiJ L n * mat g⁻¹ := by rw [antiJ_mul_antiJ_eq_one, Matrix.one_mul]
      _ = antiJ L n * (cT σ (mat g) * antiJ L n * mat g * mat g⁻¹) := by rw [hU, Matrix.mul_assoc]
      _ = antiJ L n * cT σ (mat g) * antiJ L n := by
        rw [Matrix.mul_assoc (cT σ (mat g) * antiJ L n), hinv, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [key, mul_antiJ_apply_eq_apply_rev_right, antiJ_mul_apply_eq_apply_rev_left]
  rfl

theorem rowOf_inv (u : GU σ (N + 2)) (j : Fin N) : rowOf u⁻¹ j = σ (colOf u j.rev) := by
  show mat u⁻¹ 0 (mid j) = σ (mat u (mid j.rev) (Fin.last (N + 1)))
  rw [mat_inv_apply_eq_sigma_mat_rev, mid_rev, Fin.rev_zero]

theorem cornerOf_inv (u : GU σ (N + 2)) : cornerOf u⁻¹ = σ (cornerOf u) := by
  show mat u⁻¹ 0 (Fin.last (N + 1)) = σ (mat u 0 (Fin.last (N + 1)))
  rw [mat_inv_apply_eq_sigma_mat_rev, Fin.rev_last, Fin.rev_zero]

theorem row_eq {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) (j : Fin N) : rowOf u j = -σ (colOf u j.rev) := by
  have h := congrFun (rowOf_mul hu (inv_mem hu)) j
  rw [mul_inv_cancel, rowOf_one, Pi.zero_apply, Pi.add_apply, rowOf_inv] at h
  linear_combination -h

theorem colOf_inv {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : colOf u⁻¹ = -colOf u := by
  funext i
  have h := congrFun (colOf_mul hu (inv_mem hu)) i
  rw [mul_inv_cancel, colOf_one, Pi.zero_apply, Pi.add_apply] at h
  rw [Pi.neg_apply]
  linear_combination -h

theorem corner_eq {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u := by
  have h := cornerOf_mul hu (inv_mem hu)
  rw [mul_inv_cancel, cornerOf_one, cornerOf_inv, colOf_inv hu, dotProduct_neg] at h
  linear_combination -h

private theorem mat_apply_mem_intL_of_mem_radQ_of_blocks {w : GU σ (N + 2)} (hw : w ∈ radQ σ N)
    (hr : ∀ j, rowOf w j ∈ intL L) (hb : ∀ i, colOf w i ∈ intL L) (hc : cornerOf w ∈ intL L)
    (i j : Fin (N + 2)) : mat w i j ∈ intL L := by
  rcases idx_cases i with rfl | ⟨p, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨q, rfl⟩ | rfl
  · rw [rad_zero_zero hw]; exact one_mem _
  · exact hr q
  · exact hc
  · rw [rad_mid_zero hw]; exact zero_mem _
  · rw [rad_mid_mid hw, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact hb p
  · rw [rad_last_zero hw]; exact zero_mem _
  · rw [rad_last_mid hw]; exact zero_mem _
  · rw [rad_last_last hw]; exact one_mem _

theorem mem_KU_rad (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {u : GU σ (N + 2)}
    (hu : u ∈ radQ σ N) :
    u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L := by
  have hσint : ∀ x, σ x ∈ intL L ↔ x ∈ intL L := fun x => by
    show σ x ∈ Valued.v.integer ↔ x ∈ Valued.v.integer
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, hσ]
  simp only [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf, MonoidHom.mem_range]
  constructor
  · rintro ⟨-, h, hh⟩
    have e : ∀ i j, mat u i j = (((h : GL (Fin (N + 2)) (intL L)) : Matrix (Fin (N + 2)) (Fin (N + 2)) (intL L)) i j : L) := by
      intro i j
      show ((u : GL (Fin (N + 2)) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j = _
      rw [← hh]
      rfl
    refine ⟨fun j => ?_, ?_⟩
    · show mat u 0 (mid j) ∈ intL L
      rw [e]
      exact Subtype.prop _
    · show mat u 0 (Fin.last (N + 1)) ∈ intL L
      rw [e]
      exact Subtype.prop _
  · rintro ⟨hr, hc⟩
    have hb : ∀ i, colOf u i ∈ intL L := by
      intro i
      have h1 := row_eq hu i.rev
      rw [Fin.rev_rev] at h1
      have h2 : σ (colOf u i) = -rowOf u i.rev := by rw [h1, neg_neg]
      have h3 : σ (colOf u i) ∈ intL L := by
        rw [h2]
        exact neg_mem (hr i.rev)
      exact (hσint _).1 h3
    have hu' := inv_mem hu
    have E1 := mat_apply_mem_intL_of_mem_radQ_of_blocks hu hr hb hc
    have E2 := mat_apply_mem_intL_of_mem_radQ_of_blocks hu'
      (fun j => by rw [rowOf_inv]; exact (hσint _).2 (hb _))
      (fun i => by rw [colOf_inv hu]; exact neg_mem (hb i))
      (by rw [cornerOf_inv]; exact (hσint _).2 hc)
    have inj : Function.Injective ((intL L).subtype.mapMatrix : Matrix (Fin (N + 2)) (Fin (N + 2)) (intL L) → _) :=
      fun X Y hXY => by
        ext i j
        exact congrFun (congrFun hXY i) j
    have m1 : mat u * mat u⁻¹ = 1 := by
      show mat (u * u⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    have m2 : mat u⁻¹ * mat u = 1 := by
      show mat (u⁻¹ * u) = 1
      rw [inv_mul_cancel]
      rfl
    let A : Matrix (Fin (N + 2)) (Fin (N + 2)) (intL L) := Matrix.of fun i j => ⟨mat u i j, E1 i j⟩
    let B : Matrix (Fin (N + 2)) (Fin (N + 2)) (intL L) := Matrix.of fun i j => ⟨mat u⁻¹ i j, E2 i j⟩
    have hA : (intL L).subtype.mapMatrix A = mat u := by
      ext i j
      rfl
    have hB : (intL L).subtype.mapMatrix B = mat u⁻¹ := by
      ext i j
      rfl
    have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, m1])
    have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, m2])
    refine ⟨u.2, ⟨⟨A, B, hAB, hBA⟩, ?_⟩⟩
    apply Units.ext
    exact hA

def ext (v : Fin N → L) : Fin (N + 2) → L := Fin.cons 0 (Fin.snoc (α := fun _ => L) v 0)

@[simp] theorem ext_zero (v : Fin N → L) : ext v 0 = 0 := rfl

@[simp] theorem ext_mid (v : Fin N → L) (j : Fin N) : ext v (mid j) = v j := by
  rw [GlobalTheory.CompanionTheory.InertHeis.ext, mid, Fin.cons_succ, Fin.snoc_castSucc]

@[simp] theorem ext_last (v : Fin N → L) : ext v (Fin.last (N + 1)) = 0 := by
  show Fin.cons (α := fun _ => L) (0 : L) (Fin.snoc (α := fun _ => L) v 0) (Fin.last N).succ = 0
  rw [Fin.cons_succ, Fin.snoc_last]

def heisMat (r b : Fin N → L) (c : L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i j =>
  (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j + (if i = 0 then ext r j else 0) +
    (if j = Fin.last (N + 1) then ext b i else 0) + (if i = 0 ∧ j = Fin.last (N + 1) then c else 0)

section Values

variable (r b : Fin N → L) (c : L)

theorem heis_00 : heisMat r b c 0 0 = 1 := by
  have h0 : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := fun h => last_ne_zero h.symm
  simp [heisMat, h0]

theorem heis_0m (j : Fin N) : heisMat r b c 0 (mid j) = r j := by
  have h0 : (0 : Fin (N + 2)) ≠ mid j := (mid_ne_zero j).symm
  simp [heisMat, h0, mid_ne_last j]

theorem heis_0l : heisMat r b c 0 (Fin.last (N + 1)) = c := by
  have h0 : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := fun h => last_ne_zero h.symm
  simp [heisMat, h0]

theorem heisenberg_middle_first_zero (i : Fin N) : heisMat r b c (mid i) 0 = 0 := by
  have h0 : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := fun h => last_ne_zero h.symm
  simp [heisMat, h0, mid_ne_zero i]

theorem heis_mm (i j : Fin N) : heisMat r b c (mid i) (mid j) = (1 : Matrix (Fin N) (Fin N) L) i j := by
  simp [heisMat, Matrix.one_apply, mid_injective.eq_iff, mid_ne_zero i, mid_ne_last j]

theorem heis_ml (i : Fin N) : heisMat r b c (mid i) (Fin.last (N + 1)) = b i := by
  simp [heisMat, mid_ne_zero i, mid_ne_last i]

theorem heisenberg_last_first_zero : heisMat r b c (Fin.last (N + 1)) 0 = 0 := by
  have h0 : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := fun h => last_ne_zero h.symm
  simp [heisMat, h0, last_ne_zero]

theorem heis_lm (j : Fin N) : heisMat r b c (Fin.last (N + 1)) (mid j) = 0 := by
  simp [heisMat, last_ne_zero, mid_ne_last j, (mid_ne_last j).symm]

theorem heis_ll : heisMat r b c (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by
  simp [heisMat, last_ne_zero]

end Values

theorem one_mid_mid (i j : Fin N) :
    (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) (mid j) = (1 : Matrix (Fin N) (Fin N) L) i j := by
  simp only [Matrix.one_apply, mid_injective.eq_iff]

theorem heis_unitary (hσσ : ∀ x, σ (σ x) = x) (r b : Fin N → L) (c : L) (hb : ∀ i, b i = -σ (r i.rev))
    (hc : c + σ c = -∑ j, r j * σ (r j.rev)) :
    cT σ (heisMat r b c) * antiJ L (N + 2) * heisMat r b c = antiJ L (N + 2) := by
  have h0 : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := fun h => last_ne_zero h.symm
  have hbσ : ∀ m : Fin N, σ (b m.rev) = -r m := by
    intro m
    rw [hb, Fin.rev_rev, map_neg, hσσ]
  have hσδ : ∀ p m : Fin N, σ ((1 : Matrix (Fin N) (Fin N) L) m.rev p) = (1 : Matrix (Fin N) (Fin N) L) m p.rev := by
    intro p m
    by_cases h : m = p.rev
    · subst h
      rw [Fin.rev_rev, Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne (fun h' => h (by rw [← h', Fin.rev_rev])), Matrix.one_apply_ne h, map_zero]
  ext i j
  have hrow : ∀ k, (cT σ (heisMat r b c) * antiJ L (N + 2)) i k = σ (heisMat r b c k.rev i) := by
    intro k
    rw [mul_antiJ_apply_eq_apply_rev_right]
    rfl
  rw [Matrix.mul_apply]
  simp only [hrow]
  rw [sum_idx, Fin.rev_zero, Fin.rev_last, antiJ_apply_eq_ite_rev]
  simp only [← mid_rev]
  rcases idx_cases i with rfl | ⟨p, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨q, rfl⟩ | rfl
  all_goals try simp only [← mid_rev, Fin.rev_zero, Fin.rev_last]
  · simp [heisenberg_last_first_zero, heisenberg_middle_first_zero, heis_00, h0]
  · simp [heisenberg_last_first_zero, heisenberg_middle_first_zero, heis_00, heis_lm, mid_ne_last q]
  · simp [heisenberg_last_first_zero, heisenberg_middle_first_zero, heis_00, heis_ll]
  · simp only [heis_lm, heis_mm, heisenberg_middle_first_zero, heis_0m, heisenberg_last_first_zero, map_zero, zero_mul, mul_zero,
      zero_add, add_zero, Finset.sum_const_zero, Fin.rev_zero]
    rw [if_neg (mid_ne_zero _).symm]
  · simp only [heis_lm, heis_mm, heis_0m, map_zero, zero_mul, mul_zero, zero_add, add_zero, hσδ p]
    simp only [mid_injective.eq_iff]
    by_cases h : q = p.rev
    · subst h
      simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h, Ne.symm h]
  · simp only [heis_lm, heis_ml, heis_mm, heis_0m, heis_ll, heis_0l, hσδ p, map_zero, zero_mul, zero_add, mul_one]
    rw [if_neg (mid_ne_last _).symm]
    simp [Matrix.one_apply, hb, Fin.rev_rev]
  · simp [heis_ll, heis_00, heis_ml, heisenberg_middle_first_zero, heis_0l, heisenberg_last_first_zero]
  · simp only [heis_ll, heis_0m, heis_ml, heis_mm, heis_0l, heis_lm, map_one, one_mul, mul_zero,
      add_zero, hbσ, Fin.rev_last]
    rw [if_neg (mid_ne_zero _)]
    simp [Matrix.one_apply]
  · simp only [heis_ll, heis_0l, heis_ml, map_one, one_mul, mul_one, hbσ, Fin.rev_last]
    rw [if_neg last_ne_zero]
    simp only [hb, neg_mul_neg]
    linear_combination hc

theorem Heisenberg₂ : Heis := by
  intro L _ _ ϖ σ q N hI
  obtain ⟨hσσ, hσ, -⟩ := hI
  refine ⟨fun u hu => ⟨row_eq hu, corner_eq hu, mem_KU_rad hσσ hσ hu⟩,
    fun u hu u' hu' => ⟨rowOf_mul hu hu', colOf_mul hu hu', cornerOf_mul hu hu'⟩, ?_⟩
  intro r c hc
  have hU := heis_unitary hσσ r (fun i => -σ (r i.rev)) c (fun i => rfl) hc
  have hl : (antiJ L (N + 2) * cT σ (heisMat r (fun i => -σ (r i.rev)) c) * antiJ L (N + 2)) *
      heisMat r (fun i => -σ (r i.rev)) c = 1 := by
    have hU' : cT σ (heisMat r (fun i => -σ (r i.rev)) c) * (antiJ L (N + 2) *
        heisMat r (fun i => -σ (r i.rev)) c) = antiJ L (N + 2) := by
      rw [← Matrix.mul_assoc, hU]
    simp only [Matrix.mul_assoc]
    rw [hU', antiJ_mul_antiJ_eq_one]
  have hr := mul_eq_one_comm.mp hl
  refine ⟨⟨⟨heisMat r (fun i => -σ (r i.rev)) c, _, hr, hl⟩, hU⟩, ?_, ?_, ?_⟩
  · intro i j hij
    show heisMat r (fun i => -σ (r i.rev)) c i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j
    rcases idx_cases i with rfl | ⟨p, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨q, rfl⟩ | rfl
    · rw [heis_00, Matrix.one_apply_eq]
    · rw [blk_mid, blk_zero] at hij; omega
    · rw [blk_last, blk_zero] at hij; omega
    · rw [heisenberg_middle_first_zero, Matrix.one_apply_ne (mid_ne_zero p)]
    · rw [heis_mm, one_mid_mid]
    · rw [blk_last, blk_mid] at hij; omega
    · rw [heisenberg_last_first_zero, Matrix.one_apply_ne last_ne_zero]
    · rw [heis_lm, Matrix.one_apply_ne (mid_ne_last q).symm]
    · rw [heis_ll, Matrix.one_apply_eq]
  · funext j
    exact heis_0m r _ c j
  · exact heis_0l r _ c

end GlobalTheory.CompanionTheory.InertHeis
