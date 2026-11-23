import Formalism.LocalToGlobal.ProjectiveLattices.CurveComp

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def BIRSt {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (a : Om Z), ∃ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (wsmul k wL))
    (p : MvPolynomial (Fin G.N) T.Q.c.F), p.IsHomogeneous k ∧
    MvPolynomial.aeval (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) p ≠ 0 ∧
    a * MvPolynomial.aeval (fun i => evC hG Z ((G.w i : (recB h.toLawsCore).Cusp j wL) : T.R j)) p =
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j)

def CompSplitSt : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (w : WeightFamilies.Wt D j) (g : (recB h.toLawsCore).Cusp j w),
    ∃ g' : (recB h.toLawsCore).Cusp j w,
      evC hG Z ((g' : (recB h.toLawsCore).Cusp j w) : T.R j) = evC hG Z ((g : (recB h.toLawsCore).Cusp j w) : T.R j) ∧
      ∀ Z', Z' ≠ Z → evC hG Z' ((g' : (recB h.toLawsCore).Cusp j w) : T.R j) = 0

def GenValInjSt : Prop :=
  ∀ (w : WeightFamilies.Wt D j) (g : (recB h.toLawsCore).Cusp j w),
    (∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((g : (recB h.toLawsCore).Cusp j w) : T.R j) = 0) → g = 0

end Formalism.L2.Pj
