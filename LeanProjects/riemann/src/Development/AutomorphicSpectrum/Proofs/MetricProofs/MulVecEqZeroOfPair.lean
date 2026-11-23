import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.PeriodLimit

theorem sq_mul_sum_sq_le {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) {c : ℝ} (hc : 0 < c)
    (h : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (v : Fin g → ℝ) :
    c ^ 2 * ∑ k, v k ^ 2 ≤ ∑ k, (Y *ᵥ v) k ^ 2 := by
  have h1 := h.dotProduct_mulVec_nonneg v
  rw [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul] at h1
  have h2 : 0 ≤ ∑ k, (c * v k - (Y *ᵥ v) k) ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h3 : ∑ k, (c * v k - (Y *ᵥ v) k) ^ 2
      = c ^ 2 * ∑ k, v k ^ 2 - 2 * c * (v ⬝ᵥ (Y *ᵥ v)) + ∑ k, (Y *ᵥ v) k ^ 2 := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h4 : v ⬝ᵥ v = ∑ k, v k ^ 2 := by simp [dotProduct, sq]
  rw [h4, smul_eq_mul] at h1
  nlinarith [mul_nonneg hc.le h1]

theorem coord_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (l : Fin a → ℂ) (v : Fin g → ℤ) (k : Fin g) :
    2 * Real.pi * Complex.I * (((T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k)
      = 2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k
        + ∑ j, (((B j *ᵥ v) k : ℤ) : ℂ) * l j := by
  have h : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [add_mulVec, sum_mulVec, Pi.add_apply, mul_add, Finset.sum_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mulVec, Pi.smul_apply, smul_eq_mul]
  have : (((B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k
      = (((B j *ᵥ v) k : ℤ) : ℂ) := by
    simp [mulVec, dotProduct]
  rw [this]
  field_simp

theorem exp_coord_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (l : Fin a → ℂ) (u v : Fin g → ℤ) (k : Fin g) :
    Complex.exp (2 * Real.pi * Complex.I * (((fun k => (u k : ℂ)) +
        (T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k))
      = Complex.exp (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k)
        * ∏ j, Complex.exp (l j) ^ ((B j *ᵥ v) k) := by
  rw [Pi.add_apply, mul_add, coord_eq, Complex.exp_add, Complex.exp_add, mul_comm _ (u k : ℂ),
    Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_sum]
  simp only [Complex.exp_int_mul]

theorem exp_pair_eq {a g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (l : Fin a → ℂ) (u v : Fin g → ℤ) :
    Complex.exp (∑ k, (v k : ℂ) * (2 * Real.pi * Complex.I * (((fun k => (u k : ℂ)) +
        (T + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k)))
      = Complex.exp (∑ k, (v k : ℂ) *
          (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v k : ℂ))) k))
        * ∏ j, Complex.exp (l j) ^ (v ⬝ᵥ (B j *ᵥ v)) := by
  simp only [Complex.exp_sum, Complex.exp_int_mul, exp_coord_eq, mul_zpow,
    Finset.prod_mul_distrib]
  congr 1
  simp only [← Finset.prod_zpow, ← _root_.zpow_mul, ← Complex.exp_int_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Complex.exp_sum]
  congr 1
  simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem cast_pair {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    star (fun k => (v k : ℝ)) ⬝ᵥ ((B.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun k => (v k : ℝ)))
      = ((v ⬝ᵥ (B *ᵥ v) : ℤ) : ℝ) := by
  simp [mulVec, dotProduct]

theorem pair_nonneg {g : ℕ} {B : Matrix (Fin g) (Fin g) ℤ}
    (h : (B.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) : 0 ≤ v ⬝ᵥ (B *ᵥ v) := by
  have := h.dotProduct_mulVec_nonneg (fun k => (v k : ℝ))
  rw [cast_pair] at this
  exact_mod_cast this

theorem mulVec_eq_zero_of_pair {g : ℕ} {B : Matrix (Fin g) (Fin g) ℤ}
    (h : (B.map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ) (h0 : v ⬝ᵥ (B *ᵥ v) = 0) :
    B *ᵥ v = 0 := by
  have := (h.dotProduct_mulVec_zero_iff (fun k => (v k : ℝ))).1 (by rw [cast_pair, h0]; simp)
  ext k
  have h1 := congrFun this k
  have h2 : ((B.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun k => (v k : ℝ))) k
      = (((B *ᵥ v) k : ℤ) : ℝ) := by
    simp [mulVec, dotProduct]
  rw [h2, Pi.zero_apply] at h1
  exact_mod_cast h1

theorem finite_sum_sq_le {g : ℕ} (M : ℝ) :
    {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M}.Finite := by
  refine (Set.Finite.pi' (fun _ : Fin g => Set.finite_Icc (-⌈M⌉) ⌈M⌉)).subset ?_
  intro v hv k
  have h1 : (v k : ℝ) ^ 2 ≤ M :=
    (Finset.single_le_sum (f := fun k => (v k : ℝ) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ k)).trans hv
  have h2 : v k ^ 2 ≤ ⌈M⌉ := by
    have := h1.trans (Int.le_ceil M)
    exact_mod_cast this
  constructor <;> nlinarith [sq_nonneg (v k), sq_nonneg (2 * v k - 1), sq_nonneg (2 * v k + 1), Int.le_self_sq (v k), Int.le_self_sq (-v k)]

theorem im_period {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℤ) (k : Fin g) :
    ((A.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k
      = ((((fun k => (u k : ℂ)) + A *ᵥ (fun k => (v k : ℂ)) : Fin g → ℂ)) k).im := by
  simp [mulVec, dotProduct]

theorem limit_period : ∀ (n a g : ℕ) (ha : a ≤ n) (U : Set (Fin n → ℂ)) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c : ℝ), IsOpen U → ContinuousOn τ0 U → (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → 0 < c → (∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, Complex.exp (l j) = z (Fin.castLE ha j)) → ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → ∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, z (Fin.castLE ha j) ≠ 0 → Complex.exp (l j) = z (Fin.castLE ha j)) → (∀ j, z (Fin.castLE ha j) = 0 → l j = 0) → ∀ w : Fin g → ℂ, (z, w) ∈ closure {p : (Fin n → ℂ) × (Fin g → ℂ) | p.1 ∈ U ∧ ∃ (l' : Fin a → ℂ) (u v : Fin g → ℤ), (∀ j, Complex.exp (l' j) = p.1 (Fin.castLE ha j)) ∧ p.2 = (fun k => (u k : ℂ)) + (τ0 p.1 + ∑ j, (l' j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))} → ∃ u v : Fin g → ℤ, (∀ j, z (Fin.castLE ha j) = 0 → B j *ᵥ v = 0) ∧ w = (fun k => (u k : ℂ)) + (τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ)) := by
  intro n a g ha U τ0 B c hU hτ hB hc hY z hz l hl hl0 w hw
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.1 hw
  choose hpU l' u v hl' hpw using hp
  have hz' : Tendsto (fun m => (p m).1) atTop (𝓝 z) := (continuous_fst.tendsto _).comp hlim
  have hw' : Tendsto (fun m => (p m).2) atTop (𝓝 w) := (continuous_snd.tendsto _).comp hlim
  have hτ' : Tendsto (fun m => τ0 (p m).1) atTop (𝓝 (τ0 z)) :=
    ((hτ.continuousAt (hU.mem_nhds hz)).tendsto).comp hz'

  have hbd : ∀ m, c ^ 2 * ∑ k, (v m k : ℝ) ^ 2 ≤ ∑ k, ((p m).2 k).im ^ 2 := by
    intro m
    have := sq_mul_sum_sq_le _ hc (hY _ (hpU m) (l' m) (hl' m)) (fun k => (v m k : ℝ))
    simp only [im_period _ (u m)] at this
    rw [← hpw m] at this
    exact this
  have hcont : Continuous fun x : Fin g → ℂ => ∑ k, (x k).im ^ 2 := by fun_prop
  obtain ⟨M, hM⟩ := ((hcont.tendsto w).comp hw').bddAbove_range
  have hfin : ∀ m, v m ∈ {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M / c ^ 2} := by
    intro m
    rw [Set.mem_setOf_eq, le_div_iff₀ (by positivity), mul_comm]
    exact (hbd m).trans (hM ⟨m, rfl⟩)
  obtain ⟨v0, hv0⟩ : ∃ v0, ∃ᶠ m in atTop, v m = v0 := by
    have h1 : ∃ᶠ m in atTop, ∃ v0 ∈ {v : Fin g → ℤ | ∑ k, (v k : ℝ) ^ 2 ≤ M / c ^ 2}, v m = v0 :=
      Frequently.of_forall fun m => ⟨v m, hfin m, rfl⟩
    obtain ⟨v0, -, h⟩ := (frequently_exists_finite (finite_sum_sq_le _)).1 h1
    exact ⟨v0, h⟩
  obtain ⟨φ, hφ, hφv⟩ := extraction_of_frequently_atTop hv0
  have hz2 := hz'.comp hφ.tendsto_atTop
  have hw2 := hw'.comp hφ.tendsto_atTop
  have hτ2 := hτ'.comp hφ.tendsto_atTop
  have hzj : ∀ j : Fin a, Tendsto (fun m => (p (φ m)).1 (Fin.castLE ha j)) atTop
      (𝓝 (z (Fin.castLE ha j))) := fun j => ((continuous_apply _).tendsto _).comp hz2

  have hpair : Complex.exp (∑ k, (v0 k : ℂ) * (2 * Real.pi * Complex.I * w k))
      = Complex.exp (∑ k, (v0 k : ℂ) *
          (2 * Real.pi * Complex.I * (τ0 z *ᵥ (fun k => (v0 k : ℂ))) k))
        * ∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)) := by
    have c1 : Continuous fun x : Fin g → ℂ =>
        Complex.exp (∑ k, (v0 k : ℂ) * (2 * Real.pi * Complex.I * x k)) := by fun_prop
    have c2 : Continuous fun T : Matrix (Fin g) (Fin g) ℂ => Complex.exp (∑ k, (v0 k : ℂ) *
          (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v0 k : ℂ))) k)) := by
      simp only [mulVec, dotProduct]; fun_prop
    have t3 : Tendsto (fun m => ∏ j, (p (φ m)).1 (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0))) atTop
        (𝓝 (∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)))) := by
      refine tendsto_finset_prod _ fun j _ => ?_
      obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (pair_nonneg (hB j) v0)
      simp only [hb, zpow_natCast]
      exact (hzj j).pow b
    refine tendsto_nhds_unique ((c1.tendsto w).comp hw2)
      ((((c2.tendsto _).comp hτ2).mul t3).congr fun m => ?_)
    simp only [Function.comp]
    rw [hpw (φ m), hφv m, exp_pair_eq]
    simp only [hl']
  have hker : ∀ j, z (Fin.castLE ha j) = 0 → B j *ᵥ v0 = 0 := by
    intro j hj
    refine mulVec_eq_zero_of_pair (hB j) v0 ?_
    by_contra hne
    have : ∏ j, z (Fin.castLE ha j) ^ (v0 ⬝ᵥ (B j *ᵥ v0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, _root_.zero_zpow _ hne])
    rw [this, mul_zero] at hpair
    exact Complex.exp_ne_zero _ hpair

  have hcoord : ∀ k, Complex.exp (2 * Real.pi * Complex.I * w k)
      = Complex.exp (2 * Real.pi * Complex.I * (τ0 z *ᵥ (fun k => (v0 k : ℂ))) k)
        * ∏ j, Complex.exp (l j) ^ ((B j *ᵥ v0) k) := by
    intro k
    have c1 : Continuous fun x : Fin g → ℂ =>
        Complex.exp (2 * Real.pi * Complex.I * x k) := by fun_prop
    have c2 : Continuous fun T : Matrix (Fin g) (Fin g) ℂ =>
        Complex.exp (2 * Real.pi * Complex.I * (T *ᵥ (fun k => (v0 k : ℂ))) k) := by
      simp only [mulVec, dotProduct]; fun_prop
    have t3 : Tendsto (fun m => ∏ j, (p (φ m)).1 (Fin.castLE ha j) ^ ((B j *ᵥ v0) k)) atTop
        (𝓝 (∏ j, Complex.exp (l j) ^ ((B j *ᵥ v0) k))) := by
      refine tendsto_finset_prod _ fun j _ => ?_
      by_cases hj : z (Fin.castLE ha j) = 0
      · simp [hker j hj]
      · rw [hl j hj]
        exact (hzj j).zpow₀ _ (Or.inl hj)
    refine tendsto_nhds_unique ((c1.tendsto w).comp hw2)
      ((((c2.tendsto _).comp hτ2).mul t3).congr fun m => ?_)
    simp only [Function.comp]
    rw [hpw (φ m), hφv m, exp_coord_eq]
    simp only [hl']
  have hint : ∀ k, ∃ N : ℤ, w k = N + ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) •
      (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v0 k : ℂ))) k := by
    intro k
    have h1 := hcoord k
    rw [← exp_coord_eq _ _ _ 0, Complex.exp_eq_exp_iff_exists_int] at h1
    obtain ⟨N, hN⟩ := h1
    refine ⟨N, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
    rw [hN]
    simp only [Pi.add_apply, Pi.zero_apply, Int.cast_zero, zero_add]
    ring
  choose u0 hu0 using hint
  exact ⟨u0, v0, hker, funext hu0⟩

end GlobalTheory.CompanionTheory.PeriodLimit
