import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall

noncomputable section

open IsLocalRing GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc

namespace TateSys

def sqDeg {l : ℕ} (μ : Fin l × Fin 1 → ℤ) : ℤ := ∑ p, μ p * μ p

theorem qW_mul (y : Fin 1 → ℤ) : qW !![1] (LinearMap.mul ℤ ℤ) y = y 0 * y 0 := by
  simp [qW]

theorem lin_mul {l : ℕ} (μ : Fin l × Fin 1 → ℤ) :
    ∑ i : Fin 1, lin !![1] μ ((fun _ => LinearMap.mul ℤ ℤ) i) = sqDeg μ := by
  simp [lin, qW_mul, sqDeg, Fintype.sum_prod_type]

def low (N : ℕ) {l : ℕ} (a : Fin l × Fin 1 → ℤ) (n : ℤ) : Set (Fin l × Fin 1 → ℤ) :=
  {μ | μ ∈ orbit ℤ 3 N (LinearMap.id : ℤ →ₗ[ℤ] ℤ) a ∧ sqDeg μ < n}

theorem low_finite (N : ℕ) {l : ℕ} (a : Fin l × Fin 1 → ℤ) (n : ℤ) : (low N a n).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin l × Fin 1 => Set.Icc (-n) n) fun _ => Set.finite_Icc _ _).subset ?_
  rintro μ ⟨-, hμ⟩ p -
  have h1 : μ p * μ p ≤ sqDeg μ :=
    Finset.single_le_sum (f := fun p => μ p * μ p) (fun p _ => mul_self_nonneg _) (Finset.mem_univ p)
  have h2 : |μ p| ≤ μ p * μ p := by
    rcases eq_or_ne (μ p) 0 with h | h
    · simp [h]
    · rw [← abs_mul_abs_self]; exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs h)
  exact abs_le.1 (by linarith)

def lowF (N : ℕ) {l : ℕ} (a : Fin l × Fin 1 → ℤ) (n : ℤ) : Finset (Fin l × Fin 1 → ℤ) := (low_finite N a n).toFinset

theorem mem_lowF {N l : ℕ} {a : Fin l × Fin 1 → ℤ} {n : ℤ} {μ} :
    μ ∈ lowF N a n ↔ μ ∈ orbit ℤ 3 N (LinearMap.id : ℤ →ₗ[ℤ] ℤ) a ∧ sqDeg μ < n := by
  simp [lowF, low]

theorem term_eq {l : ℕ} (μ : Fin l × Fin 1 → ℤ) :
    (∏ i, (1 : PowerSeries ℚ) * mono !![1] (fun _ : Fin 1 => PowerSeries.X) (fun _ => LinearMap.mul ℤ ℤ)
      (fun v => μ (i, v))) = PowerSeries.X ^ (sqDeg μ).toNat := by
  simp only [one_mul, mono, qW_mul, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have : sqDeg μ = ((∑ i : Fin l, (μ (i, 0) * μ (i, 0)).toNat : ℕ) : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (mul_self_nonneg (μ (i, 0)))]
    simp [sqDeg, Fintype.sum_prod_type]
  rw [this, Int.toNat_natCast]

theorem X_mem : (PowerSeries.X : PowerSeries ℚ) ∈ maximalIdeal (PowerSeries ℚ) := by
  rw [PowerSeries.maximalIdeal_eq_span_X]; exact Ideal.mem_span_singleton_self _

theorem term_mem {l : ℕ} (μ : Fin l × Fin 1 → ℤ) {e : ℕ} (h : (e : ℤ) ≤ sqDeg μ) :
    (∏ i, (1 : PowerSeries ℚ) * mono !![1] (fun _ : Fin 1 => PowerSeries.X) (fun _ => LinearMap.mul ℤ ℤ)
      (fun v => μ (i, v))) ∈ maximalIdeal (PowerSeries ℚ) ^ e := by
  rw [term_eq]
  exact Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow X_mem _)

end TateSys

open TateSys in

def VSys.tate : VSys (O := ℤ) id 1 !![1] 3 (PowerSeries ℚ) where
  posW := by
    unfold PosW
    have : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) = Matrix.diagonal fun _ => 2 := by
      ext i j
      fin_cases i; fin_cases j; simp
    rw [this, Matrix.posDef_diagonal_iff]
    intro _; norm_num
  Y := PUnit
  V _ := PowerSeries ℚ
  ring _ := inferInstance
  dom _ := inferInstance
  loc _ := inferInstance
  cn _ := ⟨inferInstance, inferInstance, inferInstance, algebraRat.charZero _⟩
  ev _ := RingHom.id _
  ev_loc _ := inferInstance
  X _ := ℤ
  add _ := inferInstance
  mod _ := inferInstance
  fin _ := inferInstance
  proj _ := inferInstance
  freeZ _ := inferInstance
  finZ _ := inferInstance
  rank_le _ := by simp
  m _ := 1
  t _ _ := PowerSeries.X
  t_mem _ _ := ⟨X_mem, PowerSeries.X_ne_zero⟩
  δ _ _ := LinearMap.mul ℤ ℤ
  bal _ _ := ⟨fun y z => by simp [mul_comm], fun a y z => by simp [mul_left_comm, mul_assoc]⟩
  nonneg _ _ x := by simpa using mul_self_nonneg x
  pos _ x hx := ⟨0, by simpa using mul_self_pos.2 hx⟩
  Q := Unit
  u _ _ _ := 1
  u_unit _ _ := ⟨(), isUnit_one⟩
  lam := ⟨1, fun _ _ _ x hx => ⟨PowerSeries.X, X_mem, dvd_pow_self _ (by
    have : 0 < x * x := mul_self_pos.2 hx
    simp only [LinearMap.mul_apply', one_mul]; omega)⟩⟩
  four y₀ N₀ := by
    refine ⟨3 * N₀, by omega, dvd_mul_right _ _, fun _ => LinearMap.id, rfl,
      fun _ => ⟨fun c x => ⟨0, by simp⟩, LinearEquiv.refl ℤ ℤ, by simp⟩, fun l a c e => ?_⟩
    refine ⟨∑ μ ∈ lowF (3 * N₀) a e, ∏ i, (1 : PowerSeries ℚ) * mono !![1] (fun _ : Fin 1 => PowerSeries.X)
      (fun _ => LinearMap.mul ℤ ℤ) (fun v => μ (i, v)), fun y j => ⟨lowF (3 * N₀) a (max j e), ?_, ?_, ?_⟩⟩
    · intro μ hμ; exact (mem_lowF.1 hμ).1
    · intro μ hμ hS
      rw [lin_mul]
      by_contra h
      exact hS (mem_lowF.2 ⟨hμ, by push_neg at h; exact lt_of_lt_of_le h (le_max_left _ _)⟩)
    · have hsub : lowF (3 * N₀) a e ⊆ lowF (3 * N₀) a (max j e) := fun μ hμ =>
        mem_lowF.2 ⟨(mem_lowF.1 hμ).1, lt_of_lt_of_le (mem_lowF.1 hμ).2 (le_max_right _ _)⟩
      apply Ideal.mem_sup_right
      rw [Ideal.map_id]
      change _ - ∑ μ ∈ lowF (3 * N₀) a (max j e), _ ∈ _
      rw [← Finset.sum_sdiff hsub, RingHom.id_apply, sub_add_cancel_right]
      refine (Ideal.neg_mem_iff _).2 (Ideal.sum_mem _ fun μ hμ => term_mem μ ?_)
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hμ
      by_contra h
      exact h2 (mem_lowF.2 ⟨(mem_lowF.1 h1).1, by push_neg at h; exact h⟩)

theorem VSys.tate_nontrivial : ∀ y, VSys.tate.m y = 1 ∧ ∀ i, VSys.tate.t y i = PowerSeries.X ∧ VSys.tate.t y i ≠ 0 :=
  fun _ => ⟨rfl, fun _ => ⟨rfl, PowerSeries.X_ne_zero⟩⟩

theorem TateSys.unit_eq_one {e : ℤ ≃ₗ[ℤ] ℤ} : e 1 = 1 ∨ e 1 = -1 := by
  have h : e 1 * e.symm 1 = 1 := by
    have := e.apply_symm_apply 1
    rw [show e.symm 1 = e.symm 1 • (1 : ℤ) by simp, map_smul, smul_eq_mul] at this
    linarith
  exact Int.eq_one_or_neg_one_of_mul_eq_one h

theorem dominant_tate : Dominant (O := ℤ) id (InvFun.minVal ℤ) 1 3 !![1] (X := ℤ) (fun _ : Fin 1 => LinearMap.mul ℤ ℤ)
    (fun _ : Fin 1 × Fin 1 => (1 : ℤ)) where
  span := by
    rw [eq_top_iff]; intro x _
    have : (1 : ℤ) ∈ Submodule.span ℤ (Set.range fun _ : Fin 1 × Fin 1 => (1 : ℤ)) :=
      Submodule.subset_span ⟨(0, 0), rfl⟩
    simpa using Submodule.smul_mem _ x this
  le β _ hβ := by
    have hlin : (lin !![1] (fun _ : Fin 1 × Fin 1 => (1 : ℤ)) β : ℝ) = β 1 1 := by simp [lin, qW]
    rw [hlin, Nat.cast_one, one_mul, InvFun.evalZ,
      (InvFun.minVal ℤ).eval_eq (n := 1) (r := LinearMap.proj 0) fun x => ⟨fun _ => x, rfl⟩]
    show sInf _ ≤ _
    have hsq : ∀ y : ℤ, β y y = y * y * β 1 1 := fun y => by
      have h1 : β y y = β (y • 1) (y • 1) := by simp
      rw [h1, LinearMap.map_smul₂, LinearMap.map_smul]; simp [mul_assoc]
    by_cases h0 : (β 1 1 : ℝ) = 0
    · rw [h0]
      refine Real.sInf_nonpos fun x ⟨⟨y, hy⟩, hx⟩ => ?_
      exfalso; apply hx; rw [← hy]
      have h00 : β 1 1 = 0 := by exact_mod_cast h0
      show (β (y 0) (y 0) : ℝ) = (β ((LinearMap.proj 0 : (Fin 1 → ℤ) →ₗ[ℤ] ℤ) 0) ((LinearMap.proj 0 : (Fin 1 → ℤ) →ₗ[ℤ] ℤ) 0) : ℝ)
      rw [hsq (y 0), h00]; simp
    · refine csInf_le ⟨0, ?_⟩ ⟨⟨fun _ => 1, rfl⟩, by
        simp only [LinearMap.proj_apply, map_zero, LinearMap.zero_apply, Int.cast_zero]; exact h0⟩
      rintro x ⟨⟨y, rfl⟩, -⟩
      show (0 : ℝ) ≤ (β (y 0) (y 0) : ℝ); exact_mod_cast hβ _
  min e _ j := by
    simp only [lin, TateSys.qW_mul, Finset.univ_unique, Finset.sum_singleton, LinearMap.mul_apply']
    rcases TateSys.unit_eq_one (e := e) with h | h <;> simp [h]
  strict e he := by
    rintro ⟨x, hx⟩
    exfalso; apply hx
    have h1 : e 1 = 1 := by
      obtain ⟨w, hw⟩ := he 1
      rcases TateSys.unit_eq_one (e := e) with h | h
      · exact h
      · rw [h] at hw; simp at hw; omega
    rw [show x = x • (1 : ℤ) by simp, map_smul, h1]

end GlobalTheory.Poinc
