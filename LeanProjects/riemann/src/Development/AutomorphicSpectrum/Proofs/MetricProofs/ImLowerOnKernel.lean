import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.ChartBlockLower

private theorem dotProduct_sum' {g a : ℕ} (v : Fin g → ℝ) (w : Fin a → Fin g → ℝ) :
    v ⬝ᵥ (∑ j, w j) = ∑ j, v ⬝ᵥ w j := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem quad_im_add_sum {a g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (s : Fin a → ℂ) (v : Fin g → ℝ) :
    v ⬝ᵥ (((τ + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im) *ᵥ v)
      = v ⬝ᵥ ((τ.map Complex.im) *ᵥ v)
        + ∑ j, (s j).im * (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
  have h : ((τ + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im)
      = τ.map Complex.im + ∑ j, (s j).im • (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext i k
    simp [Matrix.sum_apply, Complex.im_sum]
  rw [h, Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum']
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem im_lower_on_kernel : ∀ (n a g : ℕ) (ha : a ≤ n) (U : Set (Fin n → ℂ)) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c : ℝ), IsOpen U → ContinuousOn τ0 U → (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → 0 < c → (∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, Complex.exp (l j) = z (Fin.castLE ha j)) → ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → ∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, z (Fin.castLE ha j) ≠ 0 → Complex.exp (l j) = z (Fin.castLE ha j)) → (∀ j, z (Fin.castLE ha j) = 0 → l j = 0) → ∀ v : Fin g → ℝ, (∀ j, z (Fin.castLE ha j) = 0 → (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im) *ᵥ v) := by
  intro n a g ha U τ0 B c hU hτ _ _ H z hz l hl _ v hv
  classical
  let l' : ℝ → Fin a → ℂ := fun t j => if z (Fin.castLE ha j) = 0 then -(t : ℂ) else l j
  let z' : ℝ → Fin n → ℂ := fun t i => if z i = 0 then Complex.exp (-(t : ℂ)) else z i
  have hT : Filter.Tendsto z' Filter.atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hzi : z i = 0
    · have h1 : Filter.Tendsto (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) Filter.atTop
          (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      have h2 : (fun t : ℝ => z' t i) = fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) := by
        funext t
        simp [z', hzi, Complex.ofReal_exp]
      rw [h2, hzi]
      simpa using h1
    · have h2 : (fun t : ℝ => z' t i) = fun _ : ℝ => z i := by
        funext t
        simp [z', hzi]
      rw [h2]
      exact tendsto_const_nhds
  have hτc : ContinuousAt τ0 z := hτ.continuousAt (hU.mem_nhds hz)
  let φ : Matrix (Fin g) (Fin g) ℂ → ℝ := fun M => v ⬝ᵥ ((M.map Complex.im) *ᵥ v)
  have hφ : Continuous φ :=
    continuous_const.dotProduct
      ((continuous_id.matrix_map Complex.continuous_im).matrix_mulVec continuous_const)
  have hsplit : ∀ (w : Fin n → ℂ) (m : Fin a → ℂ),
      v ⬝ᵥ (((τ0 w + ∑ j, (m j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
          Complex.im) *ᵥ v)
        = φ (τ0 w) + ∑ j, (m j / (2 * Real.pi * Complex.I)).im *
            (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) :=
    fun w m => quad_im_add_sum (τ0 w) B (fun j => m j / (2 * Real.pi * Complex.I)) v
  have hsum : ∀ t : ℝ, ∑ j, (l' t j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v))
      = ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
    intro t
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hzj : z (Fin.castLE ha j) = 0
    · rw [hv j hzj]
      simp
    · simp [l', hzj]
  have hev : ∀ᶠ t in Filter.atTop, c * (v ⬝ᵥ v) ≤ φ (τ0 (z' t)) +
      ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
    filter_upwards [hT.eventually_mem (hU.mem_nhds hz)] with t ht
    have hexp : ∀ j, Complex.exp (l' t j) = z' t (Fin.castLE ha j) := by
      intro j
      by_cases hzj : z (Fin.castLE ha j) = 0
      · simp [l', z', hzj]
      · simp [l', z', hzj, hl j hzj]
    have h0 := (H (z' t) ht (l' t) hexp).dotProduct_mulVec_nonneg v
    have hstar : star v = v := by
      funext i
      exact TrivialStar.star_trivial _
    rw [hstar, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hsplit, hsum] at h0
    linarith
  have hlim : Filter.Tendsto (fun t => φ (τ0 (z' t)) +
      ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v))) Filter.atTop
      (𝓝 (φ (τ0 z) + ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)))) :=
    ((hφ.tendsto _).comp (hτc.tendsto.comp hT)).add tendsto_const_nhds
  rw [hsplit]
  exact ge_of_tendsto hlim hev

end GlobalTheory.CompanionTheory.ChartBlockLower
