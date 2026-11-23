import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW

namespace HilbertSchmidtSqEq₂

theorem hs2_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs2 g = hs g := rfl

theorem smul_seminorm_cont {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {q : Seminorm ℂ E}
    (hq : Continuous q) (c : NNReal) : Continuous (c • q) := by
  rw [Seminorm.coe_smul]
  exact hq.const_smul c

end HilbertSchmidtSqEq₂

open HilbertSchmidtSqEq₂ in
theorem e3c : SmoothMapSeminormBound := by
  classical
  intro hM e3a e3b n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD A hA hMod T hG hd Q N hQc hQg hη
  obtain ⟨m, K, I₀, hK, hmax⟩ := hM n ε (kfin ε σ) A hMod N
  have hC : ∀ e : kfin ε σ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, Sm ε σ y → ‖⟪(e : H), y⟫_ℂ‖ ≤ C * Q (T y) :=
    fun e => hη e e.2
  choose Ce hCe0 hCe using hC
  set Cs : ℝ := ∑ e ∈ I₀, Ce e with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun e _ => hCe0 e
  have h3a := e3a n ε (kfin ε σ) A hMod.gl hMod.uni hMod m
  obtain ⟨D, hDm⟩ := e3b n ε H σ hU hI E p π dπ hπ A hA T hd m
  have key : ∀ y : kfin ε σ, ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) := by
    intro y
    obtain ⟨v, hv⟩ := h3a.1 y
    set w : H := ((((1 + casimirK ε A) ^ m) y : kfin ε σ) : H) with hwdef
    have hw : Sm ε σ w := hD.1 _ (((1 + casimirK ε A) ^ m) y).2
    let F : kfin ε σ →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
      { toFun := fun η g => ⟪w, σ g (η : H)⟫_ℂ
        map_add' := fun a b => by funext g; simp [inner_add_right]
        map_smul' := fun c a => by funext g; simp [inner_smul_right] }
    have hF : ∀ (η : kfin ε σ) g, F η g = ⟪w, σ g (η : H)⟫_ℂ := fun _ _ => rfl
    have h1 : ∀ η : kfin ε σ, ContinuousOn (F η) (ReciprocityTheory.ChartRestriction.DS.UJset ε) := fun η => by
      have := (continuousOn_const (c := w) (s := UJset ε)).inner (𝕜 := ℂ) (hU.2.2 (η : H))
      exact this
    have h2 : ∀ X, ReciprocityTheory.ChartRestriction.DS.inP ε X → ∀ η : kfin ε σ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε,
        HasDerivAt (fun t : ℝ => F η (g * NormedSpace.exp (t • X))) (F (actM A X η) g) 0 := by
      intro X hX η g hg
      have hXl : X ∈ lieSet ε := hX.1
      have hg' : g ∈ UJset ε := hg
      have hη' : Sm ε σ (η : H) := hD.1 _ η.2
      have ho : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (η : H)) (dRep σ X η) 0 := by
        have := hasDerivAt_orbit hU hη' hXl 0
        rwa [zero_smul, NormedSpace.exp_zero, sigma_one hU] at this
      have h4 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp (t • X)) (η : H))) (σ g (dRep σ X η)) 0 :=
        ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 ho
      have h5 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h4
      simp only [ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at h5
      rw [hF, hA X hXl η]
      refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, hF, innerSL_apply_apply]
      rw [sigma_mul hU hg' (exp_mem_UJ hXl t)]
    have h3 : ∀ η : kfin ε σ, ∃ C : ℝ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F η g‖ ≤ C * (1 + hs2 g) ^ N := by
      intro η
      refine ⟨‖w‖ * ‖(η : H)‖, fun g hg => ?_⟩
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq]
      have e1 : ‖⟪w, σ g (η : H)⟫_ℂ‖ ≤ ‖w‖ * ‖(η : H)‖ := by
        have := norm_inner_le_norm (𝕜 := ℂ) w (σ g (η : H))
        rwa [hU.2.1 g hg' (η : H)] at this
      have e2 : (1 : ℝ) ≤ (1 + hs g) ^ N := one_le_pow₀ (by linarith [hs_nonneg g])
      calc _ ≤ ‖w‖ * ‖(η : H)‖ := e1
        _ = ‖w‖ * ‖(η : H)‖ * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
    have h5b : ∀ e ∈ I₀, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F e g‖ ≤ (Cs * Q (T w)) * (1 + hs2 g) ^ N := by
      intro e he g hg
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq, inner_sigma hU hg' w (e : H), norm_inner_symm]
      have hgi : g⁻¹ ∈ UJset ε := inv_mem_UJ hg'
      have e1 := hCe e (σ g⁻¹ w) (Sm.translate hU hw hgi)
      rw [hG.1 g⁻¹ hgi w hw] at e1
      have e2 := hQg g⁻¹ hgi (T w)
      rw [hs_inv hg'] at e2
      have e3 : Ce e ≤ Cs := Finset.single_le_sum (f := Ce) (fun x _ => hCe0 x) he
      have hQ0 : 0 ≤ Q (T w) := apply_nonneg _ _
      have hW0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
      calc _ ≤ Ce e * Q (π g⁻¹ (T w)) := e1
        _ ≤ Ce e * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_left e2 (hCe0 e)
        _ ≤ Cs * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_right e3 (mul_nonneg hW0 hQ0)
        _ = _ := by ring
    have hmv := hmax F h1 h2 h3 (Cs * Q (T w)) (mul_nonneg hCs0 (apply_nonneg _ _)) h5b v
    rw [hv, hF, sigma_one hU] at hmv
    have hin : ⟪w, (v : H)⟫_ℂ = ⟪(y : H), (y : H)⟫_ℂ := by
      rw [hwdef, ← Submodule.coe_inner, ← Submodule.coe_inner, h3a.2 y v, hv]
    have hn : ‖⟪(y : H), (y : H)⟫_ℂ‖ = ‖(y : H)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow]; simp
    rw [hin, hn] at hmv
    have hTw : T w = D (T y) := hDm y
    rw [hTw] at hmv
    have hy0 : 0 ≤ ‖(y : H)‖ := norm_nonneg _
    have hR0 : 0 ≤ K * Cs * Q (D (T y)) := mul_nonneg (mul_nonneg hK hCs0) (apply_nonneg _ _)
    rcases hy0.eq_or_lt with h0 | h0
    · rw [← h0]; exact hR0
    · have : ‖(y : H)‖ * ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) * ‖(y : H)‖ := by
        have e : K * (Cs * Q (D (T y))) * ‖(y : H)‖ = K * Cs * Q (D (T y)) * ‖(y : H)‖ := by ring
        rw [← e, ← sq]
        exact hmv
      exact le_of_mul_le_mul_right this h0
  refine ⟨(K * Cs).toNNReal • Q.comp (D : E →ₗ[ℂ] E), smul_seminorm_cont ?_ _, fun v hv => ?_⟩
  · rw [Seminorm.coe_comp]
    exact hQc.comp D.continuous
  · rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (mul_nonneg hK hCs0),
      Seminorm.comp_apply]
    exact key ⟨v, hv⟩

end PositivityTheory.CW

end
