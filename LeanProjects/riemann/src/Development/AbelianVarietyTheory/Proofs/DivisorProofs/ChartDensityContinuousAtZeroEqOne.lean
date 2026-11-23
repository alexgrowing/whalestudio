import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.DensOne

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * (G.map τ * x.map (starRingEnd ℂ)) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem det_ne_zero_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (mat x τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
  exact_mod_cast sgn_ne X.p0 (a : ℕ)

theorem densF_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    densF X x = fun w => ∏ τ, ∏ i : Fin r, ‖lminor (Gw X w τ) i.castSucc‖ ^ (-2 : ℤ) := by
  funext w
  unfold densF
  simp only [dmin_cpt_orth X hx]

theorem dens_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧
      ∀ τ, (mat x τ).det ≠ 0 := by
  intro E _ _ _ r X x hx
  refine ⟨?_, ?_, det_ne_zero_of_orth X hx⟩
  · rw [densF_orth X hx]
    refine tendsto_finset_prod _ fun τ _ => tendsto_finset_prod _ fun i _ => ?_
    refine ((cont_lminor X τ i.castSucc).norm.continuousAt).zpow₀ _ (Or.inl ?_)
    simp [norm_lminor_zero]
  · rw [densF_orth X hx]
    simp only [norm_lminor_zero, _root_.one_zpow, Finset.prod_const_one]

end GlobalTheory.DensOne
