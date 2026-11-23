import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities

noncomputable section

namespace GlobalTheory.BigRec

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

def PhRec {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (σ : T.Q.c.F →+* ℂ) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (i : ℕ)
    (et : (recB h.toLawsCore).Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j i)) (c : ℝ) : Prop :=
  ∀ k : (T.U j σ).Comp, ∃ ph : Frame ((T.U j σ).X k).Ψ D.R.r → ℝ,
    (∀ x ∈ ((T.U j σ).X k).dom, 0 ≤ ph x) ∧
    (∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).la1 x < ε0 →
      ca / ((T.U j σ).X k).la1 x ^ 2 ≤ ph x) ∧
    InterpolationModelInequalities ((T.U j σ).X k) (laU (T.U j σ) (wtA wL) wL.n k)
      (laU (T.U j σ) (wtA (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j i)) (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j i).n k)
      (fun m => rdU (T.U j σ) (w m).1 k) (rdU (T.U j σ) et.1 k) c i ph

end GlobalTheory.BigRec
