import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfA

namespace GlobalTheory.ScalarPoin

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def laS (X : Data E r) (k : ℕ) : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then (k : ℤ) else -(k : ℤ)

def qS (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x : Frame X.Ψ r) : ℂ :=
  ∏ τ, ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k

theorem qS_pow (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x : Frame X.Ψ r) :
    qS X x0 k x = qS X x0 1 x ^ k := by
  simp only [qS, pow_one, Finset.prod_pow]

theorem qS_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)) :
    qS X x0 k (cpt X x0 z) = 1 := by
  unfold qS
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [KU.Mx_cpt X ho, KU.tl_nM₂₂, ExF.det_unipotentFrame_eq_one, KU.tl, Matrix.det_submatrix_equiv_self, ExF.det_nM]
  simp

end

end GlobalTheory.ScalarPoin
