import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace MCLogDetGramDeriv

def constK (g k : ℕ) : ℝ := (k.factorial : ℝ) * k * ((g : ℝ) ^ 2) ^ k * ((g : ℝ) ^ 2 + 2) + 1

theorem constK_pos (g k : ℕ) : 0 < constK g k := by
  unfold constK; positivity

theorem key_bound (g k : ℕ) (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    (k.factorial : ℝ) * k * ((g : ℝ) ^ 2 * a ^ 2 * x) ^ (k - 1) *
        ((g : ℝ) ^ 2 * (2 * a ^ 2 * x + a ^ 2 * ((g : ℝ) ^ 2 * x ^ 2 * b))) ≤
      constK g k * (1 + a) ^ (2 * k) * (1 + x) ^ (k + 1) * (1 + b) := by
  rcases k with _ | n
  · simp only [Nat.cast_zero, mul_zero, zero_mul]
    have := constK_pos g 0
    positivity
  · simp only [Nat.add_sub_cancel]
    have hx1 : 1 ≤ 1 + x := by linarith
    have hA : (a ^ 2) ^ n * a ^ 2 ≤ (1 + a) ^ (2 * (n + 1)) := by
      rw [← pow_succ, pow_mul]
      gcongr
      linarith
    have hX1 : x ^ (n + 1) ≤ (1 + x) ^ (n + 1 + 1) :=
      (pow_le_pow_left₀ hx (by linarith) _).trans (pow_le_pow_right₀ hx1 (by omega))
    have hX2 : x ^ (n + 2) ≤ (1 + x) ^ (n + 1 + 1) := pow_le_pow_left₀ hx (by linarith) _
    have hbr : 2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b ≤
        ((g : ℝ) ^ 2 + 2) * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
      have h1 : 2 * x ^ (n + 1) ≤ 2 * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
        have : (1 + x) ^ (n + 1 + 1) ≤ (1 + x) ^ (n + 1 + 1) * (1 + b) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
        linarith
      have h2 : (g : ℝ) ^ 2 * x ^ (n + 2) * b ≤
          (g : ℝ) ^ 2 * ((1 + x) ^ (n + 1 + 1) * (1 + b)) := by
        rw [mul_assoc]
        gcongr
        have : 0 ≤ x ^ (n + 2) := by positivity
        nlinarith
      linarith
    have hP : 0 ≤ ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1) := by
      positivity
    have hbr0 : 0 ≤ 2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b := by positivity
    calc ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2 * a ^ 2 * x) ^ n *
          ((g : ℝ) ^ 2 * (2 * a ^ 2 * x + a ^ 2 * ((g : ℝ) ^ 2 * x ^ 2 * b)))
        = (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1)) *
            ((a ^ 2) ^ n * a ^ 2) * (2 * x ^ (n + 1) + (g : ℝ) ^ 2 * x ^ (n + 2) * b) := by
          ring
      _ ≤ (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1)) *
            (1 + a) ^ (2 * (n + 1)) * (((g : ℝ) ^ 2 + 2) * ((1 + x) ^ (n + 1 + 1) * (1 + b))) := by
          gcongr
      _ = (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) * ((g : ℝ) ^ 2) ^ (n + 1) *
            ((g : ℝ) ^ 2 + 2)) * ((1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b)) := by
          ring
      _ ≤ constK g (n + 1) * ((1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b)) := by
          gcongr
          unfold constK
          push_cast
          linarith
      _ = constK g (n + 1) * (1 + a) ^ (2 * (n + 1)) * (1 + x) ^ (n + 1 + 1) * (1 + b) := by ring

end MCLogDetGramDeriv

open MCLogDetGramDeriv in

theorem LogDetGramDeriv.proof (h₁ : InvEntryBound.Statement) (h₂ : InvEntryDeriv.Statement)
    (h₃ : MatrixDetDeriv.Statement) (h₄ : GramEntryDeriv.Statement) :
    LogDetGramDeriv.Statement := by
  intro g k
  refine ⟨constK g k, constK_pos g k, ?_⟩
  intro E _ _ F Y p a b c μ hc hμ ha hb hF hY hYc hdet
  have hZ : ∀ j l, DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p ∧ |(Y p)⁻¹ j l| ≤ c⁻¹ ∧
      ‖fderiv ℝ (fun q => (Y q)⁻¹ j l) p‖ ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b := fun j l =>
    ⟨(h₂ g Y p c b hc hYc hY j l).1, h₁ g (Y p) c hc hYc j l, (h₂ g Y p c b hc hYc hY j l).2⟩
  have hG := h₄ g k F (fun q => (Y q)⁻¹) p a c⁻¹ ((g : ℝ) ^ 2 * c⁻¹ ^ 2 * b) hF hZ
  have hD := h₃ k (fun q => (F q)ᴴ * (Y q)⁻¹.map (fun x : ℝ => (x : ℂ)) * F q) p
    ((g : ℝ) ^ 2 * a ^ 2 * c⁻¹)
    ((g : ℝ) ^ 2 * (2 * a ^ 2 * c⁻¹ + a ^ 2 * ((g : ℝ) ^ 2 * c⁻¹ ^ 2 * b))) hG
  set d : E → ℂ := fun q => ((F q)ᴴ * (Y q)⁻¹.map (fun x : ℝ => (x : ℂ)) * F q).det with hd_def
  have hpos : 0 < (d p).re := lt_of_lt_of_le hμ hdet
  have hre : HasFDerivAt (fun q => (d q).re) (Complex.reCLM.comp (fderiv ℝ d p)) p := by
    have := Complex.reCLM.hasFDerivAt.comp p hD.1.hasFDerivAt
    simpa [Function.comp_def] using this
  have hL := hre.log hpos.ne'
  have hfun : (fun q => logDetGram (Y q) (F q)) = fun q => Real.log (d q).re := by
    funext q; rfl
  rw [hfun]
  refine ⟨hL.differentiableAt, ?_⟩
  rw [hL.fderiv]
  have hnorm : ‖Complex.reCLM.comp (fderiv ℝ d p)‖ ≤ ‖fderiv ℝ d p‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [Complex.reCLM_norm, one_mul]
  have hkey := key_bound g k a b c⁻¹ ha hb (inv_nonneg.mpr hc.le)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  calc (d p).re⁻¹ * ‖Complex.reCLM.comp (fderiv ℝ d p)‖
      ≤ (d p).re⁻¹ * ‖fderiv ℝ d p‖ := by gcongr
    _ = ‖fderiv ℝ d p‖ / (d p).re := by ring
    _ ≤ ‖fderiv ℝ d p‖ / μ := by gcongr
    _ ≤ constK g k * (1 + a) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + b) / μ := by
      gcongr
      exact hD.2.trans hkey

end

end GroundTheory.Heights₂.Heights
