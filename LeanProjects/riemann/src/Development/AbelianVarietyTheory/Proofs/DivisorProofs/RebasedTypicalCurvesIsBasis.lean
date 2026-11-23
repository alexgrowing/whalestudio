import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

namespace GlobalTheory.DepthStages.RebaseBasis

theorem rebase_isBasis : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (G : LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (X : Matrix (Fin d) (Fin d) C),
      IsBasis G p ty γ → (∀ a b, IsIntV v (X a b)) → v X.det = 0 →
      (∀ a b, X a b ≠ 0 → ty b = ty a) →
      IsBasis G p ty (rebase G X γ) ∧
        (∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b)) ∧
        ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n := by
  intro C _ _ _ v p hp hv d h ty G γ X hB hX hdet hty
  obtain ⟨hγc, hγty, hγdet⟩ := hB
  have key : ∀ a, _ := fun a => pt6' C v p hp hv d d G γ (X a) hγc (hX a)
  have hlc : ∀ a n, G.lc p (rebase G X γ a) n = ∑ b, X a b ^ (p ^ n) • G.lc p (γ b) n :=
    fun a n => (key a).2.2.1 n
  have htan : ∀ a, tangent (rebase G X γ a) = ∑ b, X a b • tangent (γ b) := fun a => (key a).2.1
  refine ⟨⟨fun a => (key a).1, fun a => ⟨(key a).2.2.2 fun b => (hγty b).1, ?_⟩, ?_⟩, htan, hlc⟩
  · intro n c hc
    rw [hlc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hXab : X a b = 0
    · rw [hXab, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul]
    · have hb := hty a b hXab
      rw [(hγty b).2 n c (by rw [hb]; exact hc), mul_zero]
  · have hM : (Matrix.of fun a b => tangent (rebase G X γ a) b) =
        X * Matrix.of fun a b => tangent (γ a) b := by
      ext a b
      rw [Matrix.of_apply, htan, Matrix.mul_apply]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hM, Matrix.det_mul, v.map_mul, hdet, hγdet, add_zero]

end GlobalTheory.DepthStages.RebaseBasis
