import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsURepOnOfIsTau
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiPositiveDefiniteCholeskyFormula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.SphJet

private lemma posDef_inv_toMK_mul_mul_toMK {n : ℕ} {ε : Fin n → Bool} (k : KG ε)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) : ((toMK k)⁻¹ * x * toMK k).PosDef := by
  have hK : toMK k ∈ Kset ε := (mem_KG ε _).1 k.2
  have hU : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hK.1
  have hinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  rw [hinv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro v₁ v₂ hv
  have := congrArg (fun v => (toMK k)ᴴ *ᵥ v) hv
  simpa [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU] using this

private lemma norm_inner_ps_exp_le_decHS_mul {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)}
    {w : W} (hlam : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) {h : ℝ}
    (hgap : GapAtLeast ε lam h) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (u y : W) :
    ‖⟪y, ps ε lam τ w (NormedSpace.exp X) u⟫_ℂ‖ ≤
      decHS h (rkR ε) (Real.sqrt (hs X)) * ‖u‖ * ‖y‖ := by
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  have hint : ∀ v : W, Integrable (fun k : KG ε => ‖⟪v, τ (toMK k) w⟫_ℂ‖ ^ 2) (muK ε) := by
    intro v
    by_contra hn
    have hs := GlobalTheory.PsiBound.schur_norm hτ v
    rw [integral_undef hn, mul_zero] at hs
    have hv : v = 0 := by
      have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
      exact norm_eq_zero.1 this
    subst hv
    simp at hn
  have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
  rw [GlobalTheory.PsiBound.ps_entry hτ lam hP u y]
  refine GlobalTheory.PsiBound.weighted_bound (muK ε) (Module.finrank ℂ W) _ _ _ _ _ _ hM (norm_nonneg u)
    (norm_nonneg y) (fun k => GlobalTheory.PsiBound.norm_Phi_le hlam hgap hX ((mem_KG ε _).1 k.2))
    (hint y) ?_ (GlobalTheory.PsiBound.schur_norm hτ y) ?_
  · simpa only [norm_inner_symm] using hint u
  · simpa only [norm_inner_symm] using GlobalTheory.PsiBound.schur_norm hτ u

theorem ps_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  intro n ε lam W _ _ τ w hlam hτ h hgap X hX
  have hP : (NormedSpace.exp X).PosDef := GlobalTheory.Dec.FormF.exp_posDef hX
  refine ⟨fun x => ?_, ?_, ?_⟩
  ·
    rw [GlobalTheory.PsiBound.ps_entry hτ lam hP x x]
    set F : KG ε → ℂ := fun k => Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) *
      (⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) with hFdef
    have hF : ∀ k, 0 ≤ F k := by
      intro k
      have hphi : 0 < Phi lam ((toMK k)⁻¹ * NormedSpace.exp X * toMK k) :=
        (phiPos n lam _ (posDef_inv_toMK_mul_mul_toMK k hP)).2.1
      have hsq : 0 ≤ ⟪x, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ := by
        rw [← inner_conj_symm x (τ (toMK k) w), mul_comm, Complex.mul_conj]
        exact Complex.zero_le_real.2 (Complex.normSq_nonneg _)
      exact mul_nonneg hphi.le hsq
    have hre : ∀ k, F k = ((F k).re : ℂ) := fun k =>
      Complex.ext rfl (by simpa using ((Complex.le_def.1 (hF k)).2).symm)
    have hI : ∫ k, F k ∂(muK ε) = ((∫ k, (F k).re ∂(muK ε) : ℝ) : ℂ) := by
      rw [integral_congr_ae (Eventually.of_forall hre)]
      first
        | exact integral_complex_ofReal
        | exact integral_ofReal
    rw [hI]
    refine mul_nonneg (Nat.cast_nonneg _) (Complex.zero_le_real.2 (integral_nonneg fun k => ?_))
    exact (Complex.le_def.1 (hF k)).1
  ·
    have hM : 0 ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := (Real.exp_pos _).le
    refine ContinuousLinearMap.opNorm_le_bound _ hM fun u => ?_
    set T := ps ε lam τ w (NormedSpace.exp X)
    rcases eq_or_ne (T u) 0 with h0 | h0
    · rw [h0, norm_zero]; positivity
    have hb := norm_inner_ps_exp_le_decHS_mul hlam hτ hgap hX u (T u)
    rw [inner_self_eq_norm_sq_to_K] at hb
    simp only [norm_pow, RCLike.norm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_norm] at hb
    have hpos : 0 < ‖T u‖ := norm_pos_iff.2 h0
    nlinarith
  ·
    obtain ⟨hopen, hpos, hdiff, -⟩ := psBasic n ε lam W τ w hlam hτ
    haveI : FiniteDimensional ℂ W := hτ.1
    haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
    let e : (Fin n → Fin n → ℂ) ≃L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      (Matrix.ofLinearEquiv ℂ).toContinuousLinearEquiv
    have hg : AnalyticAt ℂ (fun z : Fin n → Fin n → ℂ => ps ε lam τ w (Matrix.of z))
        (e.symm (NormedSpace.exp X)) :=
      GlobalTheory.SCV.analyticAt_of_differentiableOn hdiff
        (hopen.mem_nhds (show Matrix.of _ ∈ U1 ε from hpos _ hP))
    have he : AnalyticAt ℂ (⇑e.symm) (NormedSpace.exp X) :=
      e.symm.toContinuousLinearMap.analyticAt _
    exact hg.comp he

end GlobalTheory.SphJet
