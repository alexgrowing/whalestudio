import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem msOf_ex {K : Type} [Field K] [NumberField K] {n : ℕ} (Λ : (K →+* ℂ) → Multiset ℂ) (h : ∀ τ, (Λ τ).card = n) :
    ∃ L : Ix K n → ℂ, msOf L = Λ := by
  have : ∀ τ, ∃ f : Fin n → ℂ, Finset.univ.val.map f = Λ τ := by
    intro τ
    have h1 := h τ
    induction hm : Λ τ using Quotient.inductionOn with
    | _ a =>
      rw [hm] at h1
      have h2 : a.length = n := by simpa using h1
      subst h2
      exact ⟨a.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩
  choose f hf using this
  exact ⟨fun x => f x.1 x.2, funext hf⟩

private theorem val_congr {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Set (Pl K)) (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t t' : Pl K → Multiset ℂ) (h : ∀ w ∉ S, t w = t' w) (P : PR K n) (hP : ∀ y ∈ P.vars, y.1 ∉ S) :
    val x Λ t P = val x Λ t' P :=
  eval₂Hom_congr' rfl (fun i hi _ => by unfold hval; rw [h _ (hP i hi)]) rfl

private theorem arith (C w zN zi q r kM e B E1 E2 kk f g1 g2 : ℝ) (hw : 0 ≤ w) (hzN : 0 ≤ zN) (hzi : 0 ≤ zi) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hkM : 0 ≤ kM) (he : 0 ≤ e) (hB : 0 ≤ B) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hkk : 0 ≤ kk) (hf : 0 < f)
    (hg1 : 1 ≤ g1) (hg2 : 1 ≤ g2) (h1 : w * zN ≤ E1 * g1) (h2 : w * zi ≤ E2) (h3 : q ≤ B * e) (h4 : r ≤ B * e / f)
    (h5 : kM ≤ kk * g2) :
    C * w * (zN * (q + kM * r) + kM * zi * q) ≤ |C| * e * g1 * g2 * B * (E1 * (1 + kk / f) + kk * E2) := by
  have g1' : 0 ≤ g1 := zero_le_one.trans hg1
  have g2' : 0 ≤ g2 := zero_le_one.trans hg2
  have h2' : w * zi ≤ g1 * E2 := h2.trans (le_mul_of_one_le_left hE2 hg1)
  have h3' : q ≤ g2 * (B * e) := h3.trans (le_mul_of_one_le_left (by positivity) hg2)
  have hC := le_abs_self C
  calc _ = C * (w * zN * (q + kM * r) + kM * (w * zi) * q) := by ring
    _ ≤ |C| * (w * zN * (q + kM * r) + kM * (w * zi) * q) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ |C| * (E1 * g1 * (g2 * (B * e) + kk * g2 * (B * e / f)) + kk * g2 * (g1 * E2) * (B * e)) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
theorem UpperTheory.ConvolutionTheory.Ci.sideEst :
    OneSide → EvVal → TruncSpec → ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n l : ℕ), 0 < n →
      ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ l) (ev : PR K n →+* (LL μ →L[ℂ] LL μ)),
      𝔰.toAmp.IsEv ev → (∀ P, Inner μ (ev P)) → ∀ C₀ : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ χ : ℝ → ℝ, Continuous χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x ≥ η, χ x = 1) →
      ∃ s : Finset (ℝ × Submodule ℂ (LL μ)),
        (∀ y, y ∈ s ↔ η < y.1 ∧ IsSummand μ y.2 ∧ y.2.map (θ.U : LL μ →ₗ[ℂ] LL μ) = y.2 ∧ eigIn y.2 𝔰.toAmp.A y.1 ≠ ⊥) ∧
        (∀ y ∈ s, FiniteDimensional ℂ (eigIn y.2 𝔰.toAmp.A y.1)) ∧
        ∀ Φ G, admitted 𝔰.S Φ → IsGen Φ G →
          (∃ C : ℝ, ∀ d : ℕ, ‖ev (trunc d G) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)‖ ≤ C ^ (d + 1) / d.factorial) →
          ∀ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ 𝔰.S) → ∃ u : ℝ × Submodule ℂ (LL μ) → ℕ → ℂ,
            (∀ y ∈ s, ∀ (L : Ix K n → ℂ) t, At μ 𝔰.S y.2 (msOf L) t →
              Tendsto (u y) atTop (𝓝 (y.1 * val y.1 (msOf L) t P * evK L (hval t) Φ))) ∧
            ∀ (p : ℕ) (N : ℝ) (s₀ : ℕ), ∃ M : ℝ, 0 ≤ M ∧ ∀ (j d : ℕ), ∀ m ≤ s₀, ∀ m' ≤ s₀, ∀ f : TG K n,
              𝔰.Rep (ev (chebP η (j / p + m) * (trunc d G * P))) (j + m') (Real.exp (C₀ * ((j + m' : ℕ) : ℝ))) f →
              ‖twInt θ f - ∑ y ∈ s, u y d * (y.1 : ℂ) ^ d * (cheb η (j / p + m) y.1 : ℂ) *
                  trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U)‖ ≤
                M ^ (d + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / d.factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j)) := by
  intro hOS hEV hTS K _ _ _ n l hn μ _ θ 𝔰 ev hev hin C₀
  classical
  obtain ⟨N, hN⟩ := hOS K n l hn μ θ 𝔰 ev hev hin
  obtain ⟨C, hC0, hC1⟩ : ∃ C : ℝ, C₀ ≤ C ∧ 1 ≤ C := ⟨max C₀ 1, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨lu, hlu0, hlu⟩ : ∃ lu : ℝ, 0 ≤ lu ∧ ‖𝔰.Uq 0‖ ≤ Real.exp lu :=
    ⟨‖𝔰.Uq 0‖, norm_nonneg _, by linarith [Real.add_one_le_exp ‖𝔰.Uq 0‖]⟩
  refine ⟨N * C + lu, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  obtain ⟨s, hs1, hs2, hs3⟩ := hN η hη hη1 χ hχ hχ1 hχ2
  refine ⟨s, hs1, hs2, fun Φ G hΦ hG hb P hP => ?_⟩
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨⟨κ, D, hκ, hBd⟩, hu, hM⟩ := (hTS K n 𝔰.S Φ hΦ).2 G hG
  obtain ⟨Mt, hMt⟩ := hM _ ev hev.const
  have hE := fun y (hy : y ∈ s) => hEV K n hn μ 𝔰.toAmp y.2 y.1 (hη.trans ((hs1 y).1 hy).1) ((hs1 y).1 hy).2.1
  have hex : ∀ y : ℝ × Submodule ℂ (LL μ), ∃ (L : Ix K n → ℂ) (t : Pl K → Multiset ℂ), y ∈ s → At μ 𝔰.S y.2 (msOf L) t := by
    intro y
    by_cases hy : y ∈ s
    · obtain ⟨Λ, t, h⟩ := (hE y hy).1 ((hs1 y).1 hy).2.2.2
      obtain ⟨L, rfl⟩ := msOf_ex Λ fun τ => (h.1 τ).1
      exact ⟨L, t, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hy⟩
  choose L t hLt using hex
  choose u hu1 hu2 using hu
  have hT : ∀ d, ∀ y ∈ (trunc d G).vars, y.1 ∉ 𝔰.S := fun d y hy => hκ _ ((hBd d).1 y hy)
  refine ⟨fun y d => y.1 * val y.1 (msOf (L y)) (t y) P * u (L y) (t y) d, fun y hy L' t' h' => ?_, fun p N₁ s₀ => ?_⟩
  · obtain ⟨e1, e2⟩ := (hE y hy).2.1 _ _ _ _ (hLt y hy) h'
    have hy0 : (y.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hη.trans ((hs1 y).1 hy).1).ne'
    have e3 : u (L y) (t y) = u L' t' := by
      funext d
      refine mul_left_cancel₀ (pow_ne_zero d hy0) ?_
      rw [← hu2, ← hu2, e1]
      exact val_congr 𝔰.S _ _ _ _ e2 _ (hT d)
    beta_reduce
    rw [e3, e1, val_congr 𝔰.S _ _ _ _ e2 P hP]
    exact (hu1 L' t').const_mul _
  obtain ⟨N', hN'⟩ := exists_nat_ge (max N₁ 0 + lu)
  obtain ⟨C₁, hC₁⟩ := hs3 N'
  have hk : 1 ≤ 4 / η := by rw [le_div_iff₀ hη]; linarith
  have hc₁ : 0 ≤ N * C + lu := by positivity
  obtain ⟨B, hB1, hB2, hB3⟩ : ∃ B : ℝ, 1 ≤ B ∧ |Mt| ≤ B ∧ |Cb| ≤ B :=
    ⟨max 1 (max |Mt| |Cb|), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  obtain ⟨K0, hK0, hK1⟩ : ∃ K0 : ℝ, |C₁| * ‖ev P‖ * Real.exp ((N * C + lu) * s₀) * (4 / η) ^ s₀ ≤ K0 ∧ 1 ≤ K0 :=
    ⟨max _ 1, le_max_left _ _, le_max_right _ _⟩
  refine ⟨K0 * B, by positivity, fun j d m hm m' hm' f hf => ?_⟩
  have hJ0 : (0 : ℝ) ≤ ((j + m' : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJ1 : (j : ℝ) ≤ ((j + m' : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right j m'
  have hJ2 : ((j + m' : ℕ) : ℝ) ≤ j + s₀ := by exact_mod_cast Nat.add_le_add_left hm' j
  have hQv : ∀ y ∈ (trunc d G * P).vars, y.1 ∉ 𝔰.S := fun y hy => by
    rcases Finset.mem_union.1 (vars_mul _ _ hy) with h | h
    · exact hT d y h
    · exact hP y h
  have key := hC₁ (trunc d G * P) (fun y => val y.1 (msOf (L y)) (t y) (trunc d G * P))
    (fun y hy v hv => (hE y hy).2.2 ev hev _ _ (hLt y hy) _ hQv v hv) (j / p + m) (j + m')
    (Real.exp (C * ((j + m' : ℕ) : ℝ))) f (Real.one_le_exp (by positivity))
    ⟨hf.1, fun x hx => hf.2 x (lt_of_le_of_lt (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hC0 hJ0)) hx)⟩
  have es : ∑ y ∈ s, y.1 * val y.1 (msOf (L y)) (t y) P * u (L y) (t y) d * (y.1 : ℂ) ^ d * (cheb η (j / p + m) y.1 : ℂ) *
        trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U) =
      ∑ y ∈ s, (cheb η (j / p + m) y.1 : ℂ) * (y.1 * val y.1 (msOf (L y)) (t y) (trunc d G * P) *
        trOn (eigIn y.2 𝔰.toAmp.A y.1) ((𝔰.Uq 0 ^ (j + m')) ∘L Rop μ 𝔰.g ∘L θ.U)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, hu2]
    ring
  beta_reduce
  rw [es]
  refine key.trans ?_
  have hw : ‖𝔰.Uq 0‖ ^ (j + m') ≤ Real.exp (lu * ((j + m' : ℕ) : ℝ)) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) hlu _
  have hdf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have a1 : ‖𝔰.Uq 0‖ ^ (j + m') * Real.exp (C * ((j + m' : ℕ) : ℝ)) ^ N ≤
      Real.exp ((N * C + lu) * j) * Real.exp ((N * C + lu) * s₀) := by
    refine (mul_le_mul_of_nonneg_right hw (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hJ2 hc₁
    linarith
  have a2 : ‖𝔰.Uq 0‖ ^ (j + m') * (Real.exp (C * ((j + m' : ℕ) : ℝ)) ^ N')⁻¹ ≤ Real.exp (-N₁ * j) := by
    refine (mul_le_mul_of_nonneg_right hw (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have b1 : (N' : ℝ) * ((j + m' : ℕ) : ℝ) ≤ N' * (C * ((j + m' : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hJ0 hC1) (Nat.cast_nonneg _)
    have b2 := mul_le_mul_of_nonneg_right hN' hJ0
    have b3 := mul_le_mul_of_nonneg_left hJ1 (le_max_right N₁ 0)
    have b4 := mul_le_mul_of_nonneg_right (le_max_left N₁ 0) (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    linarith
  have pw : ∀ x : ℝ, |x| ≤ B → x ^ (d + 1) ≤ B ^ (d + 1) := fun x hx =>
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx _)
  have a3 : ‖ev (trunc d G * P)‖ ≤ B ^ (d + 1) * ‖ev P‖ := by
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((hMt d).trans (pw _ hB2)) (norm_nonneg _))
  have a4 : ‖ev (trunc d G * P) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)‖ ≤ B ^ (d + 1) * ‖ev P‖ / d.factorial := by
    have e : ev (trunc d G * P) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ) =
        ev P ∘L (ev (trunc d G) ∘L fcalc χ 𝔰.toAmp.A ∘L (1 - Pc μ)) := by
      rw [mul_comm, map_mul]
      rfl
    rw [e, mul_comm (B ^ (d + 1)), mul_div_assoc]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ((hCb d).trans ?_) (norm_nonneg _))
    exact div_le_div_of_nonneg_right (pw _ hB3) hdf.le
  have a5 : (4 / η) ^ (j / p + m) ≤ (4 / η) ^ (j / p) * (4 / η) ^ s₀ := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk hm) (by positivity)
  refine (arith C₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity) (norm_nonneg _) (norm_nonneg _)
    (by positivity) (norm_nonneg _) (by positivity) (by positivity) (by positivity) (by positivity) hdf
    (Real.one_le_exp (by positivity)) (one_le_pow₀ hk) a1 a2 a3 a4 a5).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (hK0.trans (le_self_pow₀ hK1 (by omega))) (by positivity)
