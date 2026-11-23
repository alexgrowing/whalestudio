import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7}

def SpanW {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (w : Fin N → B.Cusp j wL) (S : Scal B) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL

variable {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def wNorm (σ : T.Q.c.F →+* ℂ) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (p : FPt (T.U j σ).X) : ℝ :=
  Real.sqrt (∑ k, (((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA wL) wL.n p.1)
    (rdU (T.U j σ) ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) p.1) p.2) ^ 2)

def BigAt (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  NoCommonZero (Xo := T.Q.Xo j) (c := T.Q.c) (fun k => ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j)) ∧
  (∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
    Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
      evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
        evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)

def ThAt (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  ∃ (e : ℕ) (w' : WeightFamilies.Wt D j) (θ : (recB h.toLawsCore).Cusp j w'),
    wadd wF w' = wsmul e wL ∧
    ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0

def CurveInstSt : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF),
    SpanW (recPlus h j hj) G.w S → BigAt h j hj hG G → ThAt h j hj hG G g0 → (recPlus h j hj).NonZeroComp wF g0 →
    Nonempty (CurveModel G la g0)

end Formalism.L2.Pj
