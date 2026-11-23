import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Bf (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) : ℂ := ∑ a, ∑ b, v a * Gp X Z τ a b * conj (w b)

def Nv (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (m : Fin (r - X.p0)) : ℂ :=
  v (nI X m) + ∑ c, Z τ m c * v (Fin.castLE X.p0_le c)

def Pv (v : Fin r → ℂ) (a : Fin X.p0) : ℂ := v (Fin.castLE X.p0_le a)

private lemma sum_eq_sum_castLE_p0_of_vanish_above (f : Fin r → ℂ) (hf : ∀ j : Fin r, X.p0 ≤ (j : ℕ) → f j = 0) :
    ∑ j, f j = ∑ c : Fin X.p0, f (Fin.castLE X.p0_le c) := by
  let e : Fin X.p0 ↪ Fin r := ⟨Fin.castLE X.p0_le, Fin.castLE_injective X.p0_le⟩
  calc ∑ j, f j = ∑ j ∈ Finset.univ.map e, f j := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
        by_contra hlt
        exact hj (Finset.mem_map.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    _ = ∑ c, f (e c) := Finset.sum_map _ _ _
    _ = ∑ c : Fin X.p0, f (Fin.castLE X.p0_le c) := rfl

private lemma sum_eq_sum_castLE_p0_add_sum_nI (g : Fin r → ℂ) :
    ∑ c, g c = ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) + ∑ m, g (nI X m) := by
  have hr : X.p0 + (r - X.p0) = r := Nat.add_sub_cancel' X.p0_le
  rw [← Fintype.sum_equiv (finCongr hr) (fun i => g (finCongr hr i)) g (fun _ => rfl),
    Fin.sum_univ_add]
  rfl

lemma Lv_p (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (a : Fin X.p0) :
    ∑ j, X.lowBlock Z τ (Fin.castLE X.p0_le a) j * v j = v (Fin.castLE X.p0_le a) := by
  have hL : ∀ j, X.lowBlock Z τ (Fin.castLE X.p0_le a) j =
      if Fin.castLE X.p0_le a = j then 1 else 0 := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    rw [dif_neg (fun hh => absurd hh.1 (not_le.mpr (by simp))), add_zero]
  simp only [hL, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma Lv_n (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (m : Fin (r - X.p0)) :
    ∑ j, X.lowBlock Z τ (nI X m) j * v j = Nv X Z τ v m := by
  have hL : ∀ j : Fin r, X.lowBlock Z τ (nI X m) j =
      (if nI X m = j then 1 else 0) + (if h : (j : ℕ) < X.p0 then Z τ m ⟨j, h⟩ else 0) := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    congr 1
    by_cases h : (j : ℕ) < X.p0
    · rw [dif_pos ⟨(by simp [nI] : X.p0 ≤ ((nI X m : Fin r) : ℕ)), h⟩, dif_pos h]
      exact congrFun (congrArg (Z τ) (Fin.ext (by simp [nI]))) _
    · rw [dif_neg (fun hh => h hh.2), dif_neg h]
  simp only [hL, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [Nv]
  congr 1
  rw [sum_eq_sum_castLE_p0_of_vanish_above X]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [dif_pos (by simp)]
    first | rfl | (congr 2) | simp
  · intro j hj
    rw [dif_neg (not_lt.mpr hj), zero_mul]

lemma Bf_coord (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) :
    Bf X Z τ v w = ∑ a, Pv X v a * conj (Pv X w a) - ∑ m, Nv X Z τ v m * conj (Nv X Z τ w m) := by
  have hG : ∀ a b, Gp X Z τ a b =
      ∑ c : Fin r, X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * conj (X.lowBlock Z τ c b) := by
    intro a b
    simp [Gp, Matrix.mul_apply, Matrix.diagonal_apply]
  have h1 : Bf X Z τ v w = ∑ c : Fin r, ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (∑ a, X.lowBlock Z τ c a * v a) *
      conj (∑ b, X.lowBlock Z τ c b * w b) := by
    calc Bf X Z τ v w = ∑ a, ∑ b, ∑ c : Fin r, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) := by
          unfold Bf
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [hG, Finset.mul_sum, Finset.sum_mul]
      _ = ∑ a, ∑ c : Fin r, ∑ b, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c : Fin r, ∑ a, ∑ b, v a * (X.lowBlock Z τ c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) *
          conj (X.lowBlock Z τ c b)) * conj (w b) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [map_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [map_mul]
          ring
  rw [h1, sum_eq_sum_castLE_p0_add_sum_nI X, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Lv_p X, Lv_p X]
    simp [sgn, Pv]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Lv_n X, Lv_n X]
    simp [sgn, nI]

lemma Bf_sub_left (Z : X.Coord) (τ : X.Ψ) (v t w : Fin r → ℂ) :
    Bf X Z τ (v - t) w = Bf X Z τ v w - Bf X Z τ t w := by
  simp only [Bf, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma Bf_sub_right (Z : X.Coord) (τ : X.Ψ) (v t w : Fin r → ℂ) :
    Bf X Z τ w (v - t) = Bf X Z τ w v - Bf X Z τ w t := by
  simp only [Bf, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma Bf_conj (Z : X.Coord) (τ : X.Ψ) (v w : Fin r → ℂ) : Bf X Z τ w v = conj (Bf X Z τ v w) := by
  rw [Bf_coord X, Bf_coord X]
  simp only [map_sub, map_sum, map_mul, starRingEnd_self_apply]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private lemma sum_eq_add_sum_castLE_of_vanish_above {n : ℕ} (k : Fin n) (f : Fin n → ℂ) (hf : ∀ j : Fin n, k < j → f j = 0) :
    ∑ j, f j = f k + ∑ c : Fin k, f (Fin.castLE k.isLt.le c) := by
  let e : Fin k ↪ Fin n := ⟨Fin.castLE k.isLt.le, Fin.castLE_injective _⟩
  have hk : k ∉ Finset.univ.map e := by
    intro h
    obtain ⟨c, _, hc⟩ := Finset.mem_map.mp h
    have h1 := congrArg Fin.val hc
    have h2 := c.isLt
    simp only [e, Function.Embedding.coeFn_mk, Fin.coe_castLE] at h1
    omega
  calc ∑ j, f j = ∑ j ∈ insert k (Finset.univ.map e), f j := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
        by_contra hle
        push_neg at hle
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hj (Finset.mem_insert_of_mem
            (Finset.mem_map.mpr ⟨⟨(j : ℕ), hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩))
        · exact hj (by rw [heq]; exact Finset.mem_insert_self _ _)
    _ = f k + ∑ j ∈ Finset.univ.map e, f j := Finset.sum_insert hk
    _ = f k + ∑ c, f (e c) := by rw [Finset.sum_map]
    _ = f k + ∑ c : Fin k, f (Fin.castLE k.isLt.le c) := rfl

lemma Bf_gv_zero (Z : X.Coord) (τ : X.Ψ) (hdet : ∀ c : Fin r, (blk (Gp X Z τ) c).det ≠ 0) (k : Fin r)
    (t : Fin r → ℂ) (ht : ∀ b, k ≤ b → t b = 0) :
    Bf X Z τ (fun a => uMat (Gp X Z τ) a k) t = 0 := by
  have hB : IsUnit (blk (Gp X Z τ) k).det := isUnit_iff_ne_zero.mpr (hdet k)
  have hw : Matrix.vecMul (Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹)
      (blk (Gp X Z τ) k) = rowc (Gp X Z τ) k := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hB, Matrix.vecMul_one]
  show ∑ a, ∑ b, uMat (Gp X Z τ) a k * Gp X Z τ a b * conj (t b) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : k ≤ b
  · simp [ht b hb]
  · push_neg at hb
    rw [← Finset.sum_mul]
    have hcol : ∑ c : Fin k, (Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹) c *
        Gp X Z τ (Fin.castLE k.isLt.le c) b = Gp X Z τ k b := congrFun hw ⟨(b : ℕ), hb⟩
    have hu : ∀ c : Fin k, uMat (Gp X Z τ) (Fin.castLE k.isLt.le c) k =
        -(Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹) c := by
      intro c
      have hne : Fin.castLE k.isLt.le c ≠ k := by
        intro h
        have h1 := congrArg Fin.val h
        have h2 := c.isLt
        simp only [Fin.coe_castLE] at h1
        omega
      have hlt : Fin.castLE k.isLt.le c < k := Fin.lt_iff_val_lt_val.mpr (by simp)
      simp only [uMat, Matrix.of_apply, if_neg hne, dif_pos hlt]
      try rfl
    have hsum : ∑ a, uMat (Gp X Z τ) a k * Gp X Z τ a b = 0 := by
      rw [sum_eq_add_sum_castLE_of_vanish_above k]
      · rw [show uMat (Gp X Z τ) k k = 1 by simp [uMat]]
        simp only [hu, neg_mul, Finset.sum_neg_distrib]
        rw [hcol]
        ring
      · intro j hj
        simp only [uMat, Matrix.of_apply, if_neg (ne_of_gt hj), dif_neg (not_lt.mpr hj.le), zero_mul]
    rw [hsum, zero_mul]

lemma Bf_self_re (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) :
    (Bf X Z τ v v).re = nsq (Pv X v) - nsq (Nv X Z τ v) := by
  rw [Bf_coord X]
  simp only [Complex.sub_re, Complex.re_sum, nsq]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;>
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma Bf_pos_ge (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (hv : ∀ m, v (nI X m) = 0) :
    (1 - X.zN Z ^ 2) * nsq (Pv X v) ≤ (Bf X Z τ v v).re := by
  rw [Bf_self_re X]
  have hN : Nv X Z τ v = (Matrix.of (Z τ)).mulVec (Pv X v) := by
    funext m
    simp only [Nv, hv m, zero_add]
    rfl
  have h1 := nsq_mulVec_le_opN (Matrix.of (Z τ)) (Pv X v)
  have h2 := opN_le_zN X Z τ
  have h3 := opN_nonneg (Matrix.of (Z τ))
  have h4 := nsq_nonneg (Pv X v)
  rw [← hN] at h1
  have h5 : Data.opN (Matrix.of (Z τ)) ^ 2 ≤ X.zN Z ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h5 h4]

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
