import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire

open UpperTheory.ConvolutionTheory.RankTwoDescent
open Filter Topology

private theorem glue_aux (A : ℂ → ℂ)
    (h : ∀ s₀ : ℂ, ∃ (r : ℝ) (H m : ℂ → ℂ), r < s₀.re ∧
      DifferentiableOn ℂ H {s | r < s.re} ∧ DifferentiableOn ℂ m {s | r < s.re} ∧ m s₀ ≠ 0 ∧
      ∀ s : ℂ, 4 < s.re → H s = A s * m s) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 4 < s.re → F s = A s := by
  choose r H m hr hH hm hne hA using h
  have hopen : ∀ ρ : ℝ, IsOpen {z : ℂ | ρ < z.re} := fun ρ =>
    isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ a b s : ℂ, r a < s.re → r b < s.re → H a s * m b s = H b s * m a s := by
    intro a b s ha hb
    have hUc : IsPreconnected {z : ℂ | max (r a) (r b) < z.re} :=
      (convex_halfSpace_re_gt (max (r a) (r b))).isPreconnected
    have hsa : {z : ℂ | max (r a) (r b) < z.re} ⊆ {z | r a < z.re} :=
      fun z hz => show r a < z.re from lt_of_le_of_lt (le_max_left _ _) hz
    have hsb : {z : ℂ | max (r a) (r b) < z.re} ⊆ {z | r b < z.re} :=
      fun z hz => show r b < z.re from lt_of_le_of_lt (le_max_right _ _) hz
    have d1 : DifferentiableOn ℂ (fun z => H a z * m b z) {z : ℂ | max (r a) (r b) < z.re} :=
      ((hH a).mono hsa).mul ((hm b).mono hsb)
    have d2 : DifferentiableOn ℂ (fun z => H b z * m a z) {z : ℂ | max (r a) (r b) < z.re} :=
      ((hH b).mono hsb).mul ((hm a).mono hsa)
    have hz₀ : ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ) ∈ {z : ℂ | max (r a) (r b) < z.re} := by
      show max (r a) (r b) < (((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      linarith [le_max_left (max (r a) (r b)) 4]
    have h4 : ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ) ∈ {z : ℂ | (4 : ℝ) < z.re} := by
      show (4 : ℝ) < (((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      linarith [le_max_right (max (r a) (r b)) 4]
    have hev : (fun z => H a z * m b z) =ᶠ[𝓝 ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)]
        fun z => H b z * m a z := by
      filter_upwards [(hopen 4).mem_nhds h4] with z hz
      rw [hA a z hz, hA b z hz]
      ring
    exact (d1.analyticOnNhd (hopen _)).eqOn_of_preconnected_of_eventuallyEq
      (d2.analyticOnNhd (hopen _)) hUc hz₀ hev (show max (r a) (r b) < s.re from max_lt ha hb)
  refine ⟨fun s => H s s / m s s, ?_, ?_⟩
  · intro s₀
    have hU : {z : ℂ | r s₀ < z.re} ∈ 𝓝 s₀ := (hopen _).mem_nhds (hr s₀)
    have hdH : DifferentiableAt ℂ (H s₀) s₀ := (hH s₀).differentiableAt hU
    have hdm : DifferentiableAt ℂ (m s₀) s₀ := (hm s₀).differentiableAt hU
    have hne' : ∀ᶠ z in 𝓝 s₀, m s₀ z ≠ 0 := hdm.continuousAt.eventually_ne (hne s₀)
    have heq : (fun s => H s s / m s s) =ᶠ[𝓝 s₀] fun z => H s₀ z / m s₀ z := by
      filter_upwards [hU, hne'] with z hz hz'
      rw [div_eq_div_iff (hne z) hz']
      exact (key s₀ z z hz (hr z)).symm
    exact heq.differentiableAt_iff.mpr (hdH.div hdm (hne s₀))
  · intro s hs
    show H s s / m s s = A s
    rw [hA s s hs, mul_div_assoc, div_self (hne s), mul_one]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.ext_of :
    TrAdm → PerTr → Ent → Unf → PhiMem → Fac → ShiftM → Hol → NonZ → Ext := by
  intro hTr hPer hEnt hUnf hPhi hFac hSh hHol hNZ
  intro E _ _ _ D P ω χ hC hU hχ M U hNo L N φ hCh hG hW a ha hsum
  have hA := hTr E D P ω χ hC hU hχ
  have hPz := hPer E D P ω χ hC hU hχ hA M U hNo
  obtain ⟨c₁, hc₁, hZ⟩ := hUnf E D P ω χ hC hU hχ M U
  obtain ⟨c₂, hc₂, hF⟩ := hFac E D P ω χ hC hU hχ M L N hCh
  have hN := hG.pos
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine glue_aux (LSeries a) ?_
  intro s₀
  obtain ⟨k, hk⟩ := exists_nat_gt (1 - s₀.re)
  have hk' : 1 - (k : ℝ) < s₀.re := by linarith
  obtain ⟨φ', e, p, hG', hp, hne⟩ := hNZ E D P ω χ hC hU hχ hA L N φ hG hW k s₀ hk'
  obtain ⟨n, f, q, hfq, hsumM⟩ := hSh E D P ω χ hC hU hχ L N k φ' e p hG' hp
  have hAf : ∀ i, admitted D ω (f i) := fun i => hA _ (hfq i).1.mem
  have hdZ : Differentiable ℂ fun s => ∑ i, Zs M U χ (f i) (PhiN N (q i)) s :=
    Differentiable.fun_sum fun i _ =>
      hEnt E D P ω χ hC hU hχ M U (f i) (hAf i) (hPz _ (hfq i).1.mem) _ (hPhi N (q i) hN)
  have hdP : Differentiable ℂ fun s : ℂ => (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) :=
    (differentiable_id.add_const _).const_cpow (Or.inl hπ0)
  have hdG : Differentiable ℂ fun s : ℂ => (Complex.Gamma (s + ((e + k : ℕ) : ℂ)))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hdH : Differentiable ℂ fun s : ℂ => (c₁ * c₂)⁻¹ *
      ((Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) * ((Complex.Gamma (s + ((e + k : ℕ) : ℂ)))⁻¹)) *
        ∑ i, Zs M U χ (f i) (PhiN N (q i)) s :=
    ((differentiable_const _).mul (hdP.mul hdG)).mul hdZ
  refine ⟨1 - k, _, Mk D χ k φ' p, hk', hdH.differentiableOn,
    hHol E D P ω χ hC hU hχ k φ' p (hA _ hG'.mem), hne, ?_⟩
  intro s hs
  have h1 : ∀ i, Zs M U χ (f i) (PhiN N (q i)) s =
      c₁ * (c₂ * ((Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) * Complex.Gamma (s + ((e + k : ℕ) : ℂ))) *
        LSeries a s * Mk D χ 0 (f i) (q i) s) := fun i => by
    rw [hZ (f i) (hAf i) _ (hPhi N (q i) hN) s hs,
      hF (f i) (hAf i) (hfq i).1 a ha (e + k) (q i) (hfq i).2 s hs (hsum s hs)]
  have hsM := hsumM s hs
  simp only [h1]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← hsM]
  have hre : 0 < (s + ((e + k : ℕ) : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ ((e + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hΓ := Complex.Gamma_ne_zero_of_re_pos hre
  have hXY : (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) * (Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) = 1 := by
    rw [← Complex.cpow_add _ _ hπ0, add_neg_cancel, Complex.cpow_zero]
  have hc : c₁ * c₂ ≠ 0 := mul_ne_zero hc₁ hc₂
  generalize (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) = X at hXY ⊢
  generalize (Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) = Y at hXY ⊢
  generalize Complex.Gamma (s + ((e + k : ℕ) : ℂ)) = G at hΓ ⊢
  calc (c₁ * c₂)⁻¹ * (X * G⁻¹) * (c₁ * (c₂ * (Y * G) * LSeries a s * Mk D χ k φ' p s))
      = (X * Y) * ((c₁ * c₂)⁻¹ * (c₁ * c₂)) * (G⁻¹ * G) * (LSeries a s * Mk D χ k φ' p s) := by
        ring
    _ = LSeries a s * Mk D χ k φ' p s := by
        rw [hXY, inv_mul_cancel₀ hc, inv_mul_cancel₀ hΓ]
        ring
