import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Reduce
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Taylor
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AbsGrow

open PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory.BW

open Filter Topology in
private theorem taylor_seq (g : ℕ → ℝ → ℂ) (hg : ∀ k s, HasDerivAt (g k) (g (k + 1) s) s) (M A : ℝ)
    (hA0 : 0 ≤ A) (bnd0 : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ‖g k t‖ ≤ M * A ^ k) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * g k 0) (g 0 1) := by
  have key : ∀ j, iteratedDeriv j (g 0) = g j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      exact (hg j s).deriv
  have hgs : ∀ m : ℕ, ContDiff ℝ m (g 0) := by
    intro m
    have : ContDiff ℝ ((m : ℕ∞) : WithTop ℕ∞) (g 0) := by
      refine contDiff_of_differentiable_iteratedDeriv fun j _ => ?_
      rw [key]
      exact fun s => (hg j s).differentiableAt
    exact_mod_cast this
  have hsum : Summable (fun k : ℕ => ((Nat.factorial k : ℂ))⁻¹ * g k 0) := by
    have hs0 : Summable (fun k : ℕ => M * (A ^ k / (Nat.factorial k : ℝ))) :=
      (Real.summable_pow_div_factorial A).mul_left _
    refine Summable.of_norm_bounded hs0 ?_
    intro k
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have := bnd0 k 0 (by simp)
    have hf : (0 : ℝ) ≤ ((Nat.factorial k : ℝ))⁻¹ := by positivity
    calc ((Nat.factorial k : ℝ))⁻¹ * ‖g k 0‖
        ≤ ((Nat.factorial k : ℝ))⁻¹ * (M * A ^ k) := mul_le_mul_of_nonneg_left this hf
      _ = M * (A ^ k / (Nat.factorial k : ℝ)) := by ring
  have htay : ∀ m : ℕ, taylorWithinEval (g 0) m (Set.Icc 0 1) 0 1 =
      ∑ k ∈ Finset.range (m + 1), ((Nat.factorial k : ℂ))⁻¹ * g k 0 := by
    intro m
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hgs k).contDiffAt) (by simp), key]
    simp [Complex.real_smul]
  have hrem : ∀ m : ℕ, ‖g 0 1 - taylorWithinEval (g 0) m (Set.Icc 0 1) 0 1‖ ≤
      M * A * (A ^ m / (Nat.factorial m : ℝ)) := by
    intro m
    have h1 := taylor_mean_remainder_bound (f := g 0) (a := 0) (b := 1) (x := 1) (n := m)
      (C := M * A ^ (m + 1)) zero_le_one
      (by exact_mod_cast (hgs (m + 1)).contDiffOn) (by simp) (by
        intro y hy
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
          ((hgs (m + 1)).contDiffAt) hy, key]
        exact bnd0 _ y hy)
    refine h1.trans (le_of_eq ?_)
    simp only [sub_zero, one_pow, mul_one]
    ring
  have hlim : Tendsto (fun m : ℕ => taylorWithinEval (g 0) m (Set.Icc 0 1) 0 1) atTop (𝓝 (g 0 1)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun m : ℕ => M * A * (A ^ m / (Nat.factorial m : ℝ)))
        atTop (𝓝 0) := by
      simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop A).const_mul (M * A)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) h0
    rw [norm_sub_rev]
    exact hrem m
  rw [hsum.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
  simpa only [htay] using hlim

private theorem line_deriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f f' : E → ℂ) (w : E)
    (h : ∀ x, HasDerivAt (fun s : ℝ => f (x + s • w)) (f' x) 0) (x : E) (u : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • w)) (f' (x + u • w)) u := by
  have h1 := h (x + u • w)
  have h2 : HasDerivAt (fun s : ℝ => f (x + u • w + s • w)) (f' (x + u • w)) (u + -u) := by
    simpa using h1
  have h3 := h2.comp_add_const u (-u)
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp only [add_smul, neg_smul]
  congr 1
  abel

private theorem mv_bound (g g' : ℝ → ℂ) (h : ∀ u, HasDerivAt g (g' u) u) (s B : ℝ)
    (hB : ∀ u, |u| ≤ |s| → ‖g' u‖ ≤ B) : ‖g s - g 0‖ ≤ B * |s| := by
  have := (convex_closedBall (0 : ℝ) |s|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (C := B) (x := 0) (y := s) (fun u _ => (h u).hasDerivWithinAt)
    (fun u hu => hB u (by simpa using hu)) (by simp) (by simp)
  simpa using this

private theorem line_lip {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f f' : E → ℂ) (w : E)
    (h : ∀ x, HasDerivAt (fun s : ℝ => f (x + s • w)) (f' x) 0)
    (hb : ∀ R : ℝ, ∃ B : ℝ, ∀ x, ‖x‖ ≤ R → ‖f' x‖ ≤ B) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (y : E) (s : ℝ), ‖y‖ ≤ R → |s| ≤ 1 → ‖f (y + s • w) - f y‖ ≤ B * |s| := by
  obtain ⟨B, hB⟩ := hb (R + ‖w‖)
  refine ⟨max B 0, le_max_right _ _, fun y s hy hs => ?_⟩
  have := mv_bound _ _ (line_deriv f f' w h y) s (max B 0) (fun u hu => (hB _ ?_).trans (le_max_left _ _))
  · simpa using this
  · refine (norm_add_le _ _).trans (add_le_add hy ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hu.trans hs)

open Filter Topology Asymptotics in
private theorem line_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f f1 f2 f21 f22 : E → ℂ) (w1 w2 : E)
    (h1 : ∀ x, HasDerivAt (fun s : ℝ => f (x + s • w1)) (f1 x) 0)
    (h2 : ∀ x, HasDerivAt (fun s : ℝ => f (x + s • w2)) (f2 x) 0)
    (h21 : ∀ x, HasDerivAt (fun s : ℝ => f2 (x + s • w1)) (f21 x) 0)
    (h22 : ∀ x, HasDerivAt (fun s : ℝ => f2 (x + s • w2)) (f22 x) 0)
    (b21 : ∀ R : ℝ, ∃ B : ℝ, ∀ x, ‖x‖ ≤ R → ‖f21 x‖ ≤ B)
    (b22 : ∀ R : ℝ, ∃ B : ℝ, ∀ x, ‖x‖ ≤ R → ‖f22 x‖ ≤ B) (x : E) :
    HasDerivAt (fun s : ℝ => f (x + s • (w1 + w2))) (f1 x + f2 x) 0 := by
  obtain ⟨B1, hB1, l1⟩ := line_lip f2 f21 w1 h21 b21 ‖x‖
  obtain ⟨B2, hB2, l2⟩ := line_lip f2 f22 w2 h22 b22 (‖x‖ + ‖w1‖)
  have hq : ∀ s : ℝ, |s| ≤ 1 →
      ‖f (x + s • w1 + s • w2) - f (x + s • w1) - s • f2 x‖ ≤ ((B1 + B2) * |s|) * |s| := by
    intro s hs
    have hy : ‖x + s • w1‖ ≤ ‖x‖ + ‖w1‖ := by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) hs
    have := mv_bound (fun u => f (x + s • w1 + u • w2) - u • f2 x)
      (fun u => f2 (x + s • w1 + u • w2) - f2 x) (fun u => by
        have := (line_deriv f f2 w2 h2 (x + s • w1) u).sub ((hasDerivAt_id u).smul_const (f2 x))
        rw [one_smul] at this
        exact this) s ((B1 + B2) * |s|) (fun u hu => by
        have a1 := l1 x s le_rfl hs
        have a2 := l2 _ u hy (hu.trans hs)
        have a3 := norm_sub_le_norm_sub_add_norm_sub (f2 (x + s • w1 + u • w2)) (f2 (x + s • w1)) (f2 x)
        have a4 := mul_le_mul_of_nonneg_left hu hB2
        linarith)
    simp only [zero_smul, add_zero, sub_zero] at this
    rwa [sub_right_comm]
  have hd : HasDerivAt (fun s : ℝ => f (x + s • w1 + s • w2) - f (x + s • w1)) (f2 x) 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simp only [zero_smul, add_zero, sub_self, sub_zero]
    refine IsBigO.trans_isLittleO (g := fun s : ℝ => s ^ 2) ?_ (isLittleO_pow_id (by norm_num))
    refine IsBigO.of_bound (B1 + B2) ?_
    have : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ 1 := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with s hs
      simpa using hs
    filter_upwards [this] with s hs
    refine (hq s hs).trans (le_of_eq ?_)
    rw [norm_pow, Real.norm_eq_abs]
    ring
  refine ((h1 x).add hd).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply, smul_add, add_assoc]
  ring

theorem UpperTheory.ConvolutionTheory.FX.abs_taylor :
    ∀ (τ κ A V : Type) [Fintype τ] [Nonempty τ] (n r : ℕ) [CommRing A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [Module A V]
    [IsScalarTower ℂ A V] (Z : τ × Fin n → A) (H : κ → A) (I : Fin r → A) (t : Multiplicative (Fin r → ℝ) →* A)
    (c : V →ₗ[ℂ] ((Fin r → ℝ) → ℂ)) (idx : Fin n → Fin r) (Λ : τ × Fin n → ℂ) (h : κ → EP (Fin r)) (good : Set κ) (C : ℝ),
    AbsSys Z H I t c idx Λ h good C → ∀ (v x : Fin r → ℝ) (φ : V), HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * c ((∑ j, (v j : ℂ) • I j) ^ k • φ) x) (c (t (Multiplicative.ofAdd v) • φ) x) := by
  intro τ κ A V _ _ n r _ _ _ _ _ _ Z H I t c idx Λ h good C hS v x φ
  classical
  have hb : ∀ (ψ : V) (R : ℝ), ∃ B : ℝ, ∀ y, ‖y‖ ≤ R → ‖c ψ y‖ ≤ B := by
    intro ψ R
    obtain ⟨B, hB⟩ := hS.bound ψ 0 R
    exact ⟨B, fun y hy => by simpa using hB 0 y hy⟩
  have hone : ∀ (j : Fin r) (ψ : V) (y : Fin r → ℝ),
      HasDerivAt (fun s : ℝ => c ψ (y + s • (Pi.single j (v j) : Fin r → ℝ))) (c (((v j : ℂ) • I j) • ψ) y) 0 := by
    intro j ψ y
    have h1 : HasDerivAt (fun s : ℝ => c ψ (y + Pi.single j s)) (c (I j • ψ) y) (0 * v j) := by
      simpa using hS.deriv j ψ y
    have h2 := h1.scomp (0 : ℝ) (hasDerivAt_mul_const (v j))
    rw [smul_assoc, map_smul, Pi.smul_apply, smul_eq_mul, ← Complex.real_smul]
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [Function.comp]
    rw [← Pi.single_smul', smul_eq_mul]
  have hdir : ∀ (S : Finset (Fin r)) (ψ : V) (y : Fin r → ℝ),
      HasDerivAt (fun s : ℝ => c ψ (y + s • ∑ j ∈ S, (Pi.single j (v j) : Fin r → ℝ)))
        (c ((∑ j ∈ S, (v j : ℂ) • I j) • ψ) y) 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro ψ y; simpa using hasDerivAt_const (0 : ℝ) (c ψ y)
    | insert j S hj ih =>
      intro ψ y
      rw [Finset.sum_insert hj, Finset.sum_insert hj, add_smul, map_add, Pi.add_apply]
      exact line_add (c ψ) _ _ _ _ _ _ (hone j ψ) (ih ψ) (hone j _) (ih _) (hb _) (hb _) y
  set T : A := ∑ j, (v j : ℂ) • I j with hT
  have hv : ∀ (ψ : V) (y : Fin r → ℝ), HasDerivAt (fun s : ℝ => c ψ (y + s • v)) (c (T • ψ) y) 0 := by
    intro ψ y
    have := hdir Finset.univ ψ y
    rwa [Finset.univ_sum_single] at this
  obtain ⟨K, hK1, hK⟩ := UpperTheory.ConvolutionTheory.FX.abs_growth τ n C
  obtain ⟨B, hB⟩ := hK κ A V r Z H I t c idx Λ h good hS φ (‖x‖ + ‖v‖)
  choose σ hσ using hS.surj
  obtain ⟨τ0⟩ := ‹Nonempty τ›
  set a : τ × Fin n → A := fun q => algebraMap ℂ A (Λ q) + I (idx q.2) with ha
  set M : ℝ := ∑ j, |v j| * (K + ‖Λ (τ0, σ j)‖) with hM
  have hgrow : ∀ (y : Fin r → ℝ), ‖y‖ ≤ ‖x‖ + ‖v‖ → ∀ (k : ℕ) (α : τ × Fin n →₀ ℕ),
      ‖c ((T ^ k * MvPolynomial.aeval a (MvPolynomial.monomial α (1 : ℂ))) • φ) y‖ ≤ B * K ^ α.degree * M ^ k := by
    intro y hy k
    induction k with
    | zero => intro α; simpa using hB α y hy
    | succ k ih =>
      intro α
      have e : T ^ (k + 1) * MvPolynomial.aeval a (MvPolynomial.monomial α (1 : ℂ)) =
          ∑ j, (v j : ℂ) • (T ^ k * MvPolynomial.aeval a
            (MvPolynomial.monomial (α + Finsupp.single (τ0, σ j) 1) (1 : ℂ)) -
            Λ (τ0, σ j) • (T ^ k * MvPolynomial.aeval a (MvPolynomial.monomial α (1 : ℂ)))) := by
        rw [pow_succ, mul_right_comm]
        conv_lhs => rw [hT, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [MvPolynomial.monomial_add_single, map_mul, pow_one, MvPolynomial.aeval_X, mul_smul_comm, ← hT]
        congr 1
        simp only [ha, hσ, Algebra.smul_def]
        ring
      rw [e, Finset.sum_smul, map_sum, Finset.sum_apply, pow_succ, ← mul_assoc, hM, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [smul_assoc, c.map_smul, Pi.smul_apply, norm_smul, sub_smul, map_sub, smul_assoc, c.map_smul, Pi.sub_apply,
        Pi.smul_apply, Complex.norm_real, Real.norm_eq_abs, ← hM]
      have i1 := ih (α + Finsupp.single (τ0, σ j) 1)
      have i2 := mul_le_mul_of_nonneg_left (ih α) (norm_nonneg (Λ (τ0, σ j)))
      rw [map_add, Finsupp.degree_single, pow_succ] at i1
      rw [← norm_smul] at i2
      have i3 := mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add i1 i2)) (abs_nonneg (v j))
      refine i3.trans (le_of_eq ?_)
      ring
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (by positivity)
  have := taylor_seq (fun k s => c (T ^ k • φ) (x + s • v)) (fun k s => by
    have := line_deriv _ _ v (hv (T ^ k • φ)) x s
    rwa [← mul_smul, ← pow_succ'] at this) B M hM0 (fun k s hs => by
    have := hgrow (x + s • v) (by
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2) k 0
    simpa using this)
  rw [hS.shift]
  simpa using this
