import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree

noncomputable section

open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Cu.YCoincidenceMatrices

variable {K : Type} [Field K]

private theorem sgn_mul_self (k : Fin 4) : sgn k * sgn k = 1 := by revert k; decide

private theorem sgn_rev (i j : Fin 4) : sgn j.rev * sgn i.rev = sgn i * sgn j := by revert i j; decide

private theorem adj_mul (X Y : M4 K) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_adj (X : M4 K) : adj (adj X) = X := by
  ext i j
  rw [adj_apply, adj_apply, sgn_rev, smul_smul, Fin.rev_rev, Fin.rev_rev, mul_mul_mul_comm, sgn_mul_self, sgn_mul_self,
    one_mul, one_smul]

private theorem adj_eq (X : M4 K) : adj X = !![X 3 3, X 2 3, -X 1 3, -X 0 3; X 3 2, X 2 2, -X 1 2, -X 0 2;
    -X 3 1, -X 2 1, X 1 1, X 0 1; -X 3 0, -X 2 0, X 1 0, X 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem adj_rows (X : M4 K) : adj X 0 0 = X 3 3 ∧ adj X 0 1 = X 2 3 ∧ adj X 0 2 = -X 1 3 ∧ adj X 0 3 = -X 0 3 ∧
    adj X 1 0 = X 3 2 ∧ adj X 1 1 = X 2 2 ∧ adj X 1 2 = -X 1 2 ∧ adj X 1 3 = -X 0 2 := by
  rw [adj_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private theorem up_mul_diag (X Y : M4 K) (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) : (X * Y) i i = X i i * Y i i := by
  have x10 := hX 1 0 (by decide); have x20 := hX 2 0 (by decide); have x21 := hX 2 1 (by decide)
  have x30 := hX 3 0 (by decide); have x31 := hX 3 1 (by decide); have x32 := hX 3 2 (by decide)
  have y10 := hY 1 0 (by decide); have y20 := hY 2 0 (by decide); have y21 := hY 2 1 (by decide)
  have y30 := hY 3 0 (by decide); have y31 := hY 3 1 (by decide); have y32 := hY 3 2 (by decide)
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> simp [x10, x20, x21, x30, x31, x32, y10, y20, y21, y30, y31, y32]

private theorem conj_mul (n A B : M4 K) (hnl : n * adj n = 1) : adj n * (A * B) * n = (adj n * A * n) * (adj n * B * n) := by
  calc adj n * (A * B) * n = adj n * A * (n * adj n) * B * n := by rw [hnl, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem low_inv (n : M4 K) (hn : IsLow n) : adj n * n = 1 ∧ n * adj n = 1 := by
  have h : adj n * n = 1 := by have := hn.1; unfold IsGSp at this; rwa [one_smul] at this
  exact ⟨h, by first | exact mul_eq_one_comm.mp h | exact (Matrix.mul_eq_one_comm_of_card_eq rfl).mp h | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp h⟩

theorem psi_mul {ι Γ : Type} [Group Γ] (P : PD ι Γ K) (v : ι) (hn : IsLow (P.n v)) (s t : Γ)
    (hs : IsUp (adj (P.n v) * P.r s * P.n v)) (ht : IsUp (adj (P.n v) * P.r t * P.n v)) (i : Fin 4) :
    P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t := by
  show (adj (P.n v) * P.r (s * t) * P.n v) i i = (adj (P.n v) * P.r s * P.n v) i i * (adj (P.n v) * P.r t * P.n v) i i
  rw [map_mul, conj_mul _ _ _ (low_inv _ hn).2, up_mul_diag _ _ hs ht]

theorem key (R n : M4 K) (ν : K) (hν : ν ≠ 0) (hR : IsGSp ν R) (hS : SuppM yY R) (hn : IsLow n)
    (hup : IsUp (adj n * R * n)) (h10 : n 1 0 ≠ 0) :
    (adj n * R * n) 0 0 * (adj n * R * n) 3 3 = ν ∧ (adj n * R * n) 1 1 * (adj n * R * n) 2 2 = ν ∧
      ((adj n * R * n) 1 1 - (adj n * R * n) 0 0) * ((adj n * R * n) 1 1 - (adj n * R * n) 3 3) = 0 := by
  generalize hu : adj n * R * n = u at hup ⊢
  obtain ⟨hln, hnl⟩ := low_inv n hn
  have hRn : R * n = n * u := by
    rw [← hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hnl, Matrix.one_mul]
  have hR' : adj R * R = ν • 1 := hR
  have huG : adj u * u = ν • 1 := by
    rw [← hu, adj_mul, adj_mul, adj_adj]
    calc adj n * (adj R * n) * (adj n * R * n) = adj n * (adj R * (n * adj n) * R) * n := by
          simp only [Matrix.mul_assoc]
      _ = ν • 1 := by rw [hnl, Matrix.mul_one, hR', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hln]
  have htr : Matrix.trace u = Matrix.trace R := by
    rw [← hu, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hnl, Matrix.one_mul]
  have z : ∀ i j : Fin 4, i ≠ j → wt i j ∉ yY → R i j = 0 := hS
  have r01 := z 0 1 (by decide) (by decide)
  have r02 := z 0 2 (by decide) (by decide)
  have r10 := z 1 0 (by decide) (by decide)
  have r13 := z 1 3 (by decide) (by decide)
  have r20 := z 2 0 (by decide) (by decide)
  have r23 := z 2 3 (by decide) (by decide)
  have r31 := z 3 1 (by decide) (by decide)
  have r32 := z 3 2 (by decide) (by decide)
  have n00 := hn.2.1 0
  have n01 := hn.2.2 0 1 (by decide); have n02 := hn.2.2 0 2 (by decide); have n03 := hn.2.2 0 3 (by decide)
  have u10 := hup 1 0 (by decide); have u20 := hup 2 0 (by decide); have u21 := hup 2 1 (by decide)
  have u30 := hup 3 0 (by decide); have u31 := hup 3 1 (by decide); have u32 := hup 3 2 (by decide)
  obtain ⟨aR00, aR01, aR02, aR03, aR10, aR11, aR12, aR13⟩ := adj_rows R
  obtain ⟨au00, au01, au02, au03, au10, au11, au12, au13⟩ := adj_rows u
  have c0 := congrFun (congrFun hRn 0) 0
  have c1 := congrFun (congrFun hRn 1) 0
  have c2 := congrFun (congrFun hRn 2) 0
  have c3 := congrFun (congrFun hRn 3) 0
  have dA := congrFun (congrFun hR' 0) 0
  have dB := congrFun (congrFun hR' 1) 1
  have p0 := congrFun (congrFun huG 0) 0
  have p1 := congrFun (congrFun huG 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, aR00, aR01, aR02,
    aR03, aR10, aR11, aR12, aR13, au00, au01, au02, au03, au10, au11, au12, au13, r01, r02, r10, r13, r20, r23, r31, r32,
    n00, n01, n02, n03, u10, u20, u21, u30, u31, u32, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
    neg_zero] at c0 c1 c2 c3 dA dB p0 p1
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four] at htr
  have hl : u 0 0 ≠ 0 := by
    intro h
    apply hν
    linear_combination -p0 + u 3 3 * h
  have hA : u 0 0 * (u 0 0 + u 3 3 - (R 0 0 + R 3 3)) = 0 := by
    linear_combination (R 3 3 - u 0 0) * c0 - R 0 3 * c3 + p0 - dA
  have hB : n 1 0 * (u 0 0 * (u 0 0 + u 3 3 - (R 1 1 + R 2 2))) = 0 := by
    linear_combination (R 2 2 - u 0 0) * c1 - R 1 2 * c2 + n 1 0 * p0 - n 1 0 * dB
  have hA' := (mul_eq_zero.mp hA).resolve_left hl
  have hB' := ((mul_eq_zero.mp ((mul_eq_zero.mp hB).resolve_left h10))).resolve_left hl
  refine ⟨by linear_combination p0, by linear_combination p1, ?_⟩
  linear_combination u 1 1 * (htr - hA' - hB') + p0 - p1

end UpperTheory.V.Cu.YCoincidenceMatrices

open UpperTheory.V.Cu.YCoincidenceMatrices in
theorem UpperTheory.V.Cu.yCoin : YCoin := by
  intro O Γ _ _ Φ K _ a P hP hS v hv
  have hν : ∀ s, a (Φ.ν s : O) ≠ 0 := fun s => ((Φ.ν s).isUnit.map a).ne_zero
  have hpt : ∀ s ∈ Φ.Gv v, P.ψ v 0 s * P.ψ v 3 s = a (Φ.ν s) ∧ P.ψ v 1 s * P.ψ v 2 s = a (Φ.ν s) ∧
      (P.ψ v 1 s - P.ψ v 0 s) * (P.ψ v 1 s - P.ψ v 3 s) = 0 := fun s hs =>
    key (P.r s) (P.n v) _ (hν s) (hP.mult s) (hS s) (hP.low v) (hP.flag v s hs) hv
  have hm : ∀ s ∈ Φ.Gv v, ∀ t ∈ Φ.Gv v, ∀ i, P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t := fun s hs t ht i =>
    psi_mul P v (hP.low v) s t (hP.flag v s hs) (hP.flag v t ht) i
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  push_neg at h1 h2
  obtain ⟨x, hx, hx'⟩ := h1
  obtain ⟨y, hy, hy'⟩ := h2
  obtain ⟨-, -, ex⟩ := hpt x hx
  obtain ⟨-, ey2, ey⟩ := hpt y hy
  obtain ⟨ex0, -, -⟩ := hpt x hx
  have hx3 : P.ψ v 1 x = P.ψ v 3 x := by
    rcases mul_eq_zero.mp ex with h | h
    · exact absurd (sub_eq_zero.mp h).symm hx'
    · exact sub_eq_zero.mp h
  have hy0 : P.ψ v 1 y = P.ψ v 0 y := by
    rcases mul_eq_zero.mp ey with h | h
    · exact sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hy'
  have hy1 : P.ψ v 1 y ≠ 0 := fun h => hν y (by rw [← ey2, h, zero_mul])
  have hx1 : P.ψ v 1 x ≠ 0 := fun h => hν x (by rw [← ex0, ← hx3, h, mul_zero])
  obtain ⟨-, -, exy⟩ := hpt (x * y) (Subgroup.mul_mem _ hx hy)
  rw [hm x hx y hy 0, hm x hx y hy 1, hm x hx y hy 3] at exy
  rcases mul_eq_zero.mp exy with h | h
  · apply hx'
    have : (P.ψ v 0 x - P.ψ v 1 x) * P.ψ v 1 y = 0 := by linear_combination P.ψ v 0 x * hy0 - h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hy1)
  · apply hy'
    have : (P.ψ v 1 y - P.ψ v 3 y) * P.ψ v 1 x = 0 := by linear_combination h - P.ψ v 3 y * hx3
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hx1)
