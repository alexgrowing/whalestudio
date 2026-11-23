import Mathlib
open Matrix Filter Topology

namespace GlobalTheory.MatSqrtNearOne

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}

theorem norm_mul_le_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_entry_le_entrywise_sup_norm A) (norm_entry_le_entrywise_sup_norm B)
    (norm_nonneg _) (norm_nonneg _)

theorem norm_add_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A + B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [Matrix.norm_le_iff (le_max_of_le_left (norm_nonneg _))]
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (norm_entry_le_entrywise_sup_norm A) (norm_entry_le_entrywise_sup_norm B))

theorem norm_sub_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A - B‖ ≤ max ‖A‖ ‖B‖ := by
  rw [sub_eq_add_neg, ← norm_neg B]
  exact norm_add_le_max_ultra A (-B)

noncomputable def iter (u : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => 0
  | k + 1 => u - iter u k * iter u k

theorem commute_iter {u a : Matrix (Fin n) (Fin n) K} (h : Commute a u) :
    ∀ k, Commute a (iter u k)
  | 0 => Commute.zero_right a
  | k + 1 => h.sub_right ((commute_iter h k).mul_right (commute_iter h k))

theorem norm_iter_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) : ∀ k, ‖iter u k‖ ≤ ‖u‖
  | 0 => by simp [iter]
  | k + 1 => by
    have ih := norm_iter_le hc k
    refine (norm_sub_le_max_ultra _ _).trans (max_le le_rfl ?_)
    calc ‖iter u k * iter u k‖ ≤ ‖iter u k‖ * ‖iter u k‖ := norm_mul_le_ultra _ _
      _ ≤ ‖u‖ * 1 := mul_le_mul ih (ih.trans hc.le) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u‖ := mul_one _

theorem matrix_sub_mul_self_sub_eq_neg_mul_of_commute (u a b : Matrix (Fin n) (Fin n) K) (h : Commute a b) :
    (u - b * b) - (u - a * a) = -((b - a) * (a + b)) := by
  rw [sub_mul, mul_add, mul_add, ← h.eq]
  abel

theorem norm_iter_diff_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) :
    ∀ k, ‖iter u (k + 1) - iter u k‖ ≤ ‖u‖ * ‖u‖ ^ k
  | 0 => by simp [iter]
  | k + 1 => by
    have hcomm : Commute (iter u k) (iter u (k + 1)) :=
      commute_iter (commute_iter (Commute.refl u) k).symm (k + 1)
    show ‖(u - iter u (k + 1) * iter u (k + 1)) - (u - iter u k * iter u k)‖ ≤ _
    rw [matrix_sub_mul_self_sub_eq_neg_mul_of_commute u _ _ hcomm, norm_neg]
    have hab : ‖iter u k + iter u (k + 1)‖ ≤ ‖u‖ :=
      (norm_add_le_max_ultra _ _).trans (max_le (norm_iter_le hc k) (norm_iter_le hc (k + 1)))
    calc ‖(iter u (k + 1) - iter u k) * (iter u k + iter u (k + 1))‖
        ≤ ‖iter u (k + 1) - iter u k‖ * ‖iter u k + iter u (k + 1)‖ := norm_mul_le_ultra _ _
      _ ≤ (‖u‖ * ‖u‖ ^ k) * ‖u‖ :=
          mul_le_mul (norm_iter_diff_le hc k) hab (norm_nonneg _) (by positivity)
      _ = ‖u‖ * ‖u‖ ^ (k + 1) := by ring

theorem tau_add (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A + B).map σ)ᵀ = (A.map σ)ᵀ + (B.map σ)ᵀ := by
  ext i j; simp

theorem tau_sub (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A - B).map σ)ᵀ = (A.map σ)ᵀ - (B.map σ)ᵀ := by
  ext i j; simp

theorem tau_mul (σ : K →+* K) (A B : Matrix (Fin n) (Fin n) K) :
    ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
  rw [Matrix.map_mul, transpose_mul]

theorem tau_one (σ : K →+* K) : ((1 : Matrix (Fin n) (Fin n) K).map σ)ᵀ = 1 := by
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]

theorem tau_smul (σ : K →+* K) (c : K) (A : Matrix (Fin n) (Fin n) K) :
    ((c • A).map σ)ᵀ = σ c • (A.map σ)ᵀ := by
  ext i j; simp

theorem exists_sqrt [CompleteSpace K] [CharZero K] (σ : K →+* K) (hσ : Continuous σ)
    (s : Matrix (Fin n) (Fin n) K)
    (hs : ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖) :
    ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K,
      a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  have h4 : (4 : K) ≠ 0 := by norm_num
  have h4p : 0 < ‖(4 : K)‖ := norm_pos_iff.2 h4
  set u : Matrix (Fin n) (Fin n) K := (4 : K)⁻¹ • (s - 1) with hu
  have hs1 : ‖s - 1‖ < ‖(4 : K)‖ := (Matrix.norm_lt_iff h4p).2 fun i j => by simpa using hs i j
  have hc : ‖u‖ < 1 := by
    rw [hu, norm_smul, norm_inv, inv_mul_lt_iff₀ h4p, mul_one]
    exact hs1
  have hcs : CauchySeq (iter u) := cauchySeq_of_le_geometric ‖u‖ ‖u‖ hc fun k => by
    rw [dist_eq_norm, norm_sub_rev]; exact norm_iter_diff_le hc k
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  have hfix : y + y * y = u := by
    have h1 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 y) := hy.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 (u - y * y)) :=
      tendsto_const_nhds.sub (hy.mul hy)
    exact eq_sub_iff_add_eq.1 (tendsto_nhds_unique h1 h2)
  refine ⟨1 + (2 : K) • y, ?_, ?_, ?_⟩
  · calc (1 + (2 : K) • y) * (1 + (2 : K) • y) = 1 + (4 : K) • (y + y * y) := by
          rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm]
          module
      _ = s := by rw [hfix, hu, smul_inv_smul₀ h4]; abel
  · intro a ha
    have hau : Commute a u := ((Commute.sub_right ha (Commute.one_right a))).smul_right _
    have hay : a * y = y * a :=
      tendsto_nhds_unique (hy.const_mul a)
        ((hy.mul_const a).congr fun k => (commute_iter hau k).eq.symm)
    exact ((Commute.one_right a).add_right ((show Commute a y from hay).smul_right (2 : K))).eq
  · intro hsσ
    have hτu : (u.map σ)ᵀ = u := by
      rw [hu, tau_smul, tau_sub, tau_one, hsσ, map_inv₀, map_ofNat]
    have hτiter : ∀ k, ((iter u k).map σ)ᵀ = iter u k := by
      intro k
      induction k with
      | zero => ext i j; simp [iter]
      | succ k ih =>
        show ((u - iter u k * iter u k).map σ)ᵀ = u - iter u k * iter u k
        rw [tau_sub, tau_mul, ih, hτu]
    have hτc : Continuous fun M : Matrix (Fin n) (Fin n) K => (M.map σ)ᵀ :=
      (continuous_id.matrix_map hσ).matrix_transpose
    have hτy : (y.map σ)ᵀ = y :=
      tendsto_nhds_unique ((hτc.tendsto y).comp hy) (hy.congr fun k => (hτiter k).symm)
    rw [tau_add, tau_one, tau_smul, hτy, map_ofNat]

end GlobalTheory.MatSqrtNearOne

namespace GlobalTheory

theorem matrix_sqrt_near_one_ultrametric :
    ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ →
      ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K,
        r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧
        ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  intro K _ _ _ _ n σ hσ
  have h4 : (4 : K) ≠ 0 := by norm_num
  refine ⟨{s | ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖}, ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ (by simp [h4])
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((continuous_id.matrix_elem i j).sub continuous_const).norm continuous_const
  · intro s hs
    exact MatSqrtNearOne.exists_sqrt σ hσ s hs

end GlobalTheory
