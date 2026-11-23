import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Cutoff

noncomputable section

theorem norm_entry_le_opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℂ) (a : m) (b : n) :
    ‖Z a b‖ ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)‖ := by
  set v : EuclideanSpace ℂ n := EuclideanSpace.single b (1 : ℂ)
  have h1 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)).le_opNorm v
  have hv : ‖v‖ = 1 := by simp [v]
  rw [hv, mul_one] at h1
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanLin Z v) a
  have h3 : (Matrix.toEuclideanLin Z v) a = Z a b := by
    simp [v, Matrix.toEuclideanLin_apply, Matrix.mulVec_single]
  rw [h3] at h2
  exact h2.trans h1

theorem gB_nonneg {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : 0 ≤ gB p0 w :=
  Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem zOf_mem_cut (X : Data E r) {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) :
    zOf X z τ ∈ {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < X.p0 → X.p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
  intro p hb ha
  have he : zOf X z τ p = zBlock X z τ ⟨p.1.1, ha⟩ ⟨p.1.2, hb⟩ := by
    simp [zBlock, nmat, zOf, p.2]
  rw [he]
  exact ((norm_entry_le_opNorm _ _ _).trans (hz τ).le)

theorem ofReal_bnd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by
  intro E _ _ _ r X z hz
  rw [bnd, ENNReal.ofReal_prod_of_nonneg (fun τ _ => gB_nonneg _ _)]
  refine le_of_eq (Finset.prod_congr rfl fun τ _ => ?_)
  rw [hB, Set.indicator_of_mem (zOf_mem_cut X hz τ)]

end

end GlobalTheory.IntBall.Cutoff
