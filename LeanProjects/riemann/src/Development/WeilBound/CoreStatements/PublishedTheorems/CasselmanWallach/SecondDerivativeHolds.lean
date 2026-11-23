import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace HilbertSchmidtNorm

variable {n : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem hasDerivAt_entry (g X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X) * Y) i j)
      ((g * NormedSpace.exp (t • X) * X * Y) i j) t := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).const_mul g).mul_const Y
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun x => x i j
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t h
  have e : (g * NormedSpace.exp (t • X) * X * Y) i j = L (g * (NormedSpace.exp (t • X) * X) * Y) := by
    show _ = (g * (NormedSpace.exp (t • X) * X) * Y) i j
    rw [mul_assoc g]
  rw [e]
  exact h2

theorem hilbert_schmidt_nonneg_alt (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem hilbert_schmidt_mul_le (g X : Matrix (Fin n) (Fin n) ℂ) : hs2 (g * X) ≤ hs2 g * hs2 X := by
  have key : ∀ i j, ‖(g * X) i j‖ ^ 2 ≤ (∑ k, ‖g i k‖ ^ 2) * (∑ k, ‖X k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(g * X) i j‖ ≤ ∑ k, ‖g i k‖ * ‖X k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    calc ‖(g * X) i j‖ ^ 2 ≤ (∑ k, ‖g i k‖ * ‖X k j‖) ^ 2 := by gcongr
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  unfold hs2
  calc ∑ i, ∑ j, ‖(g * X) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖g i k‖ ^ 2) * (∑ k, ‖X k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖g i k‖ ^ 2) * ∑ j, ∑ k, ‖X k j‖ ^ 2 := by
        rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm (f := fun j k => ‖X k j‖ ^ 2)]

theorem abs_two_inner_le (M N : Matrix (Fin n) (Fin n) ℂ) :
    |∑ i, ∑ j, 2 * inner ℝ (M i j) (N i j)| ≤ hs2 M + hs2 N := by
  unfold hs2
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have := abs_real_inner_le_norm (M i j) (N i j)
  rw [abs_mul, abs_two]
  nlinarith [sq_nonneg (‖M i j‖ - ‖N i j‖)]

theorem hasDerivAt_entry1 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X)) i j)
      ((g * NormedSpace.exp (t • X) * X) i j) t := by
  simpa using hasDerivAt_entry g X 1 t i j

theorem hd1 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hs2 (g * NormedSpace.exp (s • X)))
      (∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (t • X)) i j) ((g * NormedSpace.exp (t • X) * X) i j)) t := by
  unfold hs2
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact (hasDerivAt_entry1 g X t i j).norm_sq

theorem hd2 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (s • X)) i j)
        ((g * NormedSpace.exp (s • X) * X) i j))
      (∑ i, ∑ j, 2 * (inner ℝ ((g * NormedSpace.exp (t • X)) i j) ((g * NormedSpace.exp (t • X) * X * X) i j) +
        inner ℝ ((g * NormedSpace.exp (t • X) * X) i j) ((g * NormedSpace.exp (t • X) * X) i j))) t := by
  refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact ((hasDerivAt_entry1 g X t i j).inner ℝ (hasDerivAt_entry g X X t i j)).const_mul 2

theorem L1 (r : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    ((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * u ^ 2 ≤ r * u ^ r := by
  rcases r with _ | _ | k
  · simp
  · simp; linarith
  · have e1 : k + 1 + 1 - 1 = k + 1 := by omega
    have e2 : u ^ k * u ^ 2 = u ^ (k + 1 + 1) := by rw [← pow_add]
    rw [e1, mul_assoc, show k + 1 - 1 = k by omega, e2]
    have h0 : 0 ≤ u ^ (k + 1 + 1) := by positivity
    push_cast
    nlinarith

theorem L2 (r : ℕ) (u : ℝ) : (r : ℝ) * u ^ (r - 1) * u ≤ r * u ^ r := by
  rcases r with _ | k
  · simp
  · simp [pow_succ, mul_assoc]

end HilbertSchmidtNorm

open HilbertSchmidtNorm in
theorem heightFunctionalStatement_of_pairingProperties : B2 := by
  intro n X r
  set A : ℝ := 1 + hs2 X with hA
  set Bc : ℝ := 1 + hs2 (X * X) + 2 * hs2 X with hBc
  have hXn := hilbert_schmidt_nonneg_alt X
  have hXXn := hilbert_schmidt_nonneg_alt (X * X)
  refine ⟨r * r * A ^ 2 + r * Bc, by positivity, fun g => ?_⟩
  set h : ℝ → ℝ := fun s => hs2 (g * NormedSpace.exp (s • X)) with hh
  set h' : ℝ → ℝ := fun t => ∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (t • X)) i j)
    ((g * NormedSpace.exp (t • X) * X) i j) with hh'
  set H2 : ℝ := ∑ i, ∑ j, 2 * (inner ℝ ((g * NormedSpace.exp ((0:ℝ) • X)) i j)
    ((g * NormedSpace.exp ((0:ℝ) • X) * X * X) i j) + inner ℝ ((g * NormedSpace.exp ((0:ℝ) • X) * X) i j)
      ((g * NormedSpace.exp ((0:ℝ) • X) * X) i j)) with hH2
  have d1 : ∀ t, HasDerivAt h (h' t) t := fun t => hd1 g X t
  have d2 : HasDerivAt h' H2 0 := hd2 g X 0
  refine ⟨fun t => r * (1 + h t) ^ (r - 1) * h' t,
    r * (((r - 1 : ℕ) : ℝ) * (1 + h 0) ^ (r - 1 - 1) * h' 0) * h' 0 + r * (1 + h 0) ^ (r - 1) * H2,
    fun t => ((d1 t).const_add 1).pow r, (((d1 0).const_add 1).pow (r - 1)).const_mul (r : ℝ) |>.mul d2, ?_⟩
  have e0 : NormedSpace.exp ((0:ℝ) • X) = 1 := by simp
  have hg := hilbert_schmidt_nonneg_alt g
  have h0 : h 0 = hs2 g := by simp [hh]
  have hp : |h' 0| ≤ A * hs2 g := by
    have := abs_two_inner_le g (g * X)
    have := hilbert_schmidt_mul_le g X
    simp only [hh', e0, mul_one]
    nlinarith
  have hpp : |H2| ≤ Bc * hs2 g := by
    have k1 := abs_two_inner_le g (g * (X * X))
    have k2 := abs_two_inner_le (g * X) (g * X)
    have k3 := hilbert_schmidt_mul_le g X
    have k4 := hilbert_schmidt_mul_le g (X * X)
    have : H2 = (∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * (X * X)) i j)) +
        ∑ i, ∑ j, 2 * inner ℝ ((g * X) i j) ((g * X) i j) := by
      simp only [hH2, e0, mul_one, mul_add, Finset.sum_add_distrib, mul_assoc]
    rw [this]
    refine (abs_add_le _ _).trans ?_
    nlinarith
  rw [h0]
  set u : ℝ := 1 + hs2 g with hu
  have hu1 : 1 ≤ u := by linarith
  have hP : 0 ≤ ((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) := by positivity
  have hQ : 0 ≤ u ^ (r - 1) := by positivity
  have hr : (0 : ℝ) ≤ r := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hsq : h' 0 ^ 2 ≤ (A * u) ^ 2 := by
    have : |h' 0| ≤ A * u := hp.trans (by nlinarith)
    exact sq_le_sq' (by linarith [neg_abs_le (h' 0)]) (le_trans (le_abs_self _) this)
  have t1 : r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * h' 0) * h' 0 ≤ r * A ^ 2 * (r * u ^ r) := by
    calc r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * h' 0) * h' 0
        = r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1)) * h' 0 ^ 2 := by ring
      _ ≤ r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1)) * (A * u) ^ 2 := by gcongr
      _ = r * A ^ 2 * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * u ^ 2) := by ring
      _ ≤ r * A ^ 2 * (r * u ^ r) := mul_le_mul_of_nonneg_left (L1 r u hu1) (by positivity)
  have t2 : r * u ^ (r - 1) * H2 ≤ Bc * (r * u ^ r) := by
    have hH : H2 ≤ Bc * u := (le_abs_self _).trans (hpp.trans (by nlinarith))
    calc r * u ^ (r - 1) * H2 ≤ r * u ^ (r - 1) * (Bc * u) := by gcongr
      _ = Bc * (r * u ^ (r - 1) * u) := by ring
      _ ≤ Bc * (r * u ^ r) := mul_le_mul_of_nonneg_left (L2 r u) (by rw [hBc]; positivity)
  nlinarith

end PositivityTheory.CW

end
