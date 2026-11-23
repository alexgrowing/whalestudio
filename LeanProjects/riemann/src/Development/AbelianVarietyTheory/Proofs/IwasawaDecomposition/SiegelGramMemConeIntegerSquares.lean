import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetSquaresConeOfCompactPosDefStatement

open Matrix GlobalTheory.RedTh

noncomputable section

namespace GlobalTheory.SiegelCone

abbrev Tail {n : ℕ} (k : Fin n) : Type := {i : Fin n // k ≤ i}

def unip (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
    if i = j then {1} else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2)

theorem isCompact_unip (n : ℕ) : IsCompact (unip n) := by
  refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_singleton
  · exact isCompact_Icc

theorem mem_unip {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : GlobalTheory.RedTh.IsSiegel d u) :
    u ∈ unip n := by
  intro i _ j _
  simp only
  split_ifs with h1 h2
  · subst h1; simp [h.diag]
  · simp [h.lower i j h2]
  · have : i < j := lt_of_le_of_ne (not_lt.1 h2) h1
    exact abs_le.1 (h.upper i j this)

def tailForm {n : ℕ} (k : Fin n) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Tail k) (Tail k) ℝ :=
  (u.submatrix Subtype.val Subtype.val)ᵀ * diagonal (fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹) *
    u.submatrix Subtype.val Subtype.val

theorem continuous_tailForm {n : ℕ} (k : Fin n) : Continuous (tailForm k) := by
  unfold tailForm
  exact ((continuous_id.matrix_submatrix _ _).matrix_transpose.matrix_mul continuous_const).matrix_mul
    (continuous_id.matrix_submatrix _ _)

theorem tailForm_posDef {n : ℕ} (k : Fin n) {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ unip n) :
    (tailForm k u).PosDef := by
  have hu' : ∀ i j, u i j ∈ (if i = j then ({1} : Set ℝ) else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2)) :=
    fun i j => hu i trivial j trivial
  set v := u.submatrix (Subtype.val : Tail k → Fin n) Subtype.val
  have htri : v.BlockTriangular id := by
    intro a b hab
    have := hu' a.1 b.1
    have hne : a.1 ≠ b.1 := fun h => (ne_of_lt hab) (Subtype.ext h).symm
    simp only [hne, if_false, show b.1 < a.1 from hab, if_true, Set.mem_singleton_iff] at this
    exact this
  have hdet : v.det = 1 := by
    rw [det_of_upperTriangular htri]
    refine Finset.prod_eq_one fun a _ => ?_
    have := hu' a.1 a.1
    simpa [v] using this
  have hunit : IsUnit v := (isUnit_iff_isUnit_det v).2 (by rw [hdet]; exact isUnit_one)
  have hD : (diagonal fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹).PosDef :=
    posDef_diagonal_iff.2 fun a => by positivity
  have := hD.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hunit)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this

theorem tailForm_apply {n : ℕ} (k : Fin n) (u : Matrix (Fin n) (Fin n) ℝ) (a b : Tail k) :
    tailForm k u a b = ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m a.1 * u m b.1 else 0 := by
  rw [tailForm, mul_apply]
  simp only [mul_diagonal, transpose_apply, submatrix_apply]
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (k ≤ ·)) (p := (k ≤ ·)) (by simp)]
  refine Finset.sum_congr rfl fun c _ => by ring

end GlobalTheory.SiegelCone

namespace GlobalTheory.SiegelCone

def extZ {n : ℕ} (k : Fin n) (l : Tail k → ℤ) : Fin n → ℤ := fun i => if h : k ≤ i then l ⟨i, h⟩ else 0

theorem exists_increments {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hs : GlobalTheory.RedTh.IsSiegel d u) :
    ∃ G : Fin n → ℝ, (∀ k, 0 ≤ G k) ∧ ∀ m, d m = ((4 : ℝ) ^ (m : ℕ))⁻¹ * ∑ k, if k ≤ m then G k else 0 := by
  let F : ℕ → ℝ := fun m => if h : m < n then d ⟨m, h⟩ * 4 ^ m else 0
  let G : ℕ → ℝ := fun k => if k = 0 then F 0 else F k - F (k - 1)
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), G k = F m := by
    intro m
    induction m with
    | zero => simp [G]
    | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [G, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]; ring
  refine ⟨fun k => G k, fun k => ?_, fun m => ?_⟩
  · by_cases h0 : (k : ℕ) = 0
    · have := hs.nonneg k
      simp only [G, h0, if_true, F, dif_pos (show 0 < n from lt_of_le_of_lt (Nat.zero_le _) k.2)]
      have e : (⟨0, lt_of_le_of_lt (Nat.zero_le _) k.2⟩ : Fin n) = k := Fin.ext h0.symm
      rw [e]; positivity
    · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
      have hjn : j < n := by omega
      have hstep := hs.step ⟨j, hjn⟩ k (by simp [hj])
      have hnn := hs.nonneg ⟨j, hjn⟩
      have hdk : ∀ h, d ⟨j + 1, h⟩ = d k := fun h => congrArg d (Fin.ext hj.symm)
      have hFk : F (j + 1) = d k * 4 ^ (j + 1) := by
        simp only [F, dif_pos (show j + 1 < n by omega), hdk]
      have hFj : F j = d ⟨j, hjn⟩ * 4 ^ j := by simp only [F, dif_pos hjn]
      show 0 ≤ G (k : ℕ)
      rw [hj]
      simp only [G, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hFk, hFj, pow_succ]
      have : (0 : ℝ) ≤ 4 ^ j := by positivity
      nlinarith
  · have hsum : ∑ k : Fin n, (if k ≤ m then G k else 0) = F m := by
      have h1 : ∀ k : Fin n, (if k ≤ m then G k else 0) = (fun x : ℕ => if x ≤ (m : ℕ) then G x else 0) k :=
        fun k => by simp only [Fin.le_iff_val_le_val]
      rw [Finset.sum_congr rfl (fun k _ => h1 k), Fin.sum_univ_eq_sum_range (fun x => if x ≤ (m : ℕ) then G x else 0) n,
        ← Finset.sum_filter]
      have h2 : (Finset.range n).filter (· ≤ (m : ℕ)) = Finset.range ((m : ℕ) + 1) := by
        ext x; simp; omega
      rw [h2, htel]
    rw [hsum]
    simp only [F, dif_pos m.2, Fin.eta]
    field_simp

theorem tail_sum {n : ℕ} (k : Fin n) {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ unip n) (T : Finset (Tail k → ℤ))
    (C : (Tail k → ℤ) → ℝ)
    (hC : tailForm k u = ∑ l ∈ T, C l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ))) (i j : Fin n) :
    ∑ l ∈ T, C l * ((extZ k l i : ℝ) * (extZ k l j : ℝ)) =
      ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0 := by
  have hlow : ∀ m i, k ≤ m → ¬ k ≤ i → u m i = 0 := by
    intro m i hm hi
    have := hu m trivial i trivial
    have hlt : i < m := lt_of_lt_of_le (not_le.1 hi) hm
    simpa [hlt.ne', hlt] using this
  by_cases hi : k ≤ i
  · by_cases hj : k ≤ j
    · have := congrFun (congrFun hC ⟨i, hi⟩) ⟨j, hj⟩
      rw [tailForm_apply] at this
      rw [this]
      simp [Matrix.sum_apply, vecMulVec_apply, extZ, hi, hj]
    · simp only [extZ, dif_neg hj, Int.cast_zero, mul_zero]
      simp only [Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hm
      · rw [hlow m j hm hj, mul_zero]
      · rfl
  · simp only [extZ, dif_neg hi, Int.cast_zero, zero_mul, mul_zero, Finset.sum_const_zero]
    refine (Finset.sum_eq_zero fun m _ => ?_).symm
    split_ifs with hm
    · rw [hlow m i hm hi, mul_zero, zero_mul]
    · rfl

theorem gram_mem_cone : ∀ n : ℕ, ∃ S : Finset (Fin n → ℤ), ∀ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ),
    GlobalTheory.RedTh.IsSiegel d u → ∃ c : (Fin n → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧
      GlobalTheory.RedTh.gram d u = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  intro n
  have hK : ∀ k : Fin n, ∃ T : Finset (Tail k → ℤ), ∀ P ∈ tailForm k '' unip n, ∃ c : (Tail k → ℤ) → ℝ,
      (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ T, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := fun k =>
    GlobalTheory.T.exists_finset_squares_cone_of_compact_posDef (Tail k) (tailForm k '' unip n) ((isCompact_unip n).image (continuous_tailForm k))
      (by rintro _ ⟨u, hu, rfl⟩; exact tailForm_posDef k hu)
  choose T hT using hK
  refine ⟨Finset.univ.biUnion fun k => (T k).image (extZ k), ?_⟩
  intro d u hs
  have hu := mem_unip hs
  choose C hC0 hC using fun k => hT k _ ⟨u, hu, rfl⟩
  obtain ⟨G, hG0, hd⟩ := exists_increments hs
  refine ⟨fun l => ∑ k : Fin n, G k * ∑ l' ∈ T k, if extZ k l' = l then C k l' else 0, fun l => ?_, ?_⟩
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (hG0 k) (Finset.sum_nonneg fun l' _ => ?_)
    split_ifs
    · exact hC0 k l'
    · exact le_rfl
  ext i j
  have hL : GlobalTheory.RedTh.gram d u i j = ∑ k, G k * ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0 := by
    calc GlobalTheory.RedTh.gram d u i j = ∑ m, u m i * d m * u m j := by
          rw [GlobalTheory.RedTh.gram, mul_apply]; simp only [mul_diagonal, transpose_apply]
      _ = ∑ m : Fin n, ∑ k : Fin n, if k ≤ m then G k * (((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j) else 0 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hd m, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> ring
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          split_ifs <;> ring
  rw [hL]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  simp_rw [← tail_sum _ hu _ _ (hC _)]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' hl' => ?_
  have hmem : extZ k l' ∈ Finset.univ.biUnion fun k => (T k).image (extZ k) :=
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hl'⟩
  simp_rw [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos hmem]
  ring

end GlobalTheory.SiegelCone
