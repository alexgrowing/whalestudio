import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

abbrev CuspAt (u : WeightFamilies.Wt D j) : Type := (recB h.toLawsCore).Cusp j u

abbrev XP : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)

def GeneratesIn {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) {wL : WeightFamilies.Wt D j} {N : ℕ}
    (s : 𝓞 B.KO) (w : Fin N → B.Cusp j wL) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc s wL

def Generates {wL : WeightFamilies.Wt D j} {N : ℕ} (s : 𝓞 T.Q.c.F) (w : Fin N → CuspAt h j wL) : Prop :=
  GeneratesIn (XP h j hj) s w

def ptNorm (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) (p : FPt (T.U j σ).X) : ℝ :=
  ((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA u) u.n p.1) (rdU (T.U j σ) (F.1 : T.R j) p.1) p.2.1

def l2Norm (σ : T.Q.c.F →+* ℂ) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL)
    (p : FPt (T.U j σ).X) : ℝ :=
  Real.sqrt (∑ i, ptNorm h j σ wL (w i) p ^ 2)

def NoCommonZero {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ p : FPt (T.U j σ).X,
    ∃ i, rdU (T.U j σ) ((w i).1 : T.R j) p.1 p.2.1 ≠ 0

def FullTrdeg (hg : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ i₀, evC hg Z ((w i₀).1 : T.R j) ≠ 0 ∧
    Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F
      (Set.range fun i => evC hg Z ((w i).1 : T.R j) / evC hg Z ((w i₀).1 : T.R j))) = (WeightFamilies.dimY D j : Cardinal)

def SmallForm {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∃ (k m₀ : ℕ) (β : CuspAt h j (WeightAlgebra.wsmul k wL)), (XP h j hj).NonZeroComp (WeightAlgebra.wsmul k wL) β ∧
    ∃ C : ℝ, ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ p : FPt (T.U j σ).X,
      ptNorm h j σ (WeightAlgebra.wsmul k wL) β p ≤ C * l2Norm h j σ w p ^ k ∧
      ptNorm h j σ (WeightAlgebra.wsmul k wL) β p ^ m₀ ≤ C * l2Norm h j σ w p ^ (k * m₀ + 1)

def BigAt (hg : GenFrEx (T.Q.Xo j) T.Q.c) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  NoCommonZero h j w ∧ FullTrdeg h j hg w ∧ SmallForm h j hj w

def ExistsNonzeroCuspFormOfWeightPair (wL wF : WeightFamilies.Wt D j) : Prop :=
  ∃ w₂ : WeightFamilies.Wt D j, WeightAlgebra.IsG2 wL wF w₂ ∧ ∃ θ : CuspAt h j w₂, (XP h j hj).NonZeroComp w₂ θ

def CurveModelAt (hg : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (XP h j hj) ka wL wF)
    (S : WeightAlgebra.Scal (recB h.toLawsCore)) : Prop :=
  Generates h j hj S.sW G.w → BigAt h j hj hg G.w → ExistsNonzeroCuspFormOfWeightPair h j hj wL wF →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (g₀ : CuspAt h j wF), (XP h j hj).NonZeroComp wF g₀ →
      Nonempty (CurveModel (X := recPJ h j hj) (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g₀)

def CurveModelExists : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hg : GenFrEx (T.Q.Xo j) T.Q.c)
    (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (XP h j hj) ka wL wF) (S : WeightAlgebra.Scal (recB h.toLawsCore)),
    CurveModelAt h j hj hg G S

example : XP h j hj = recPlus h j hj := rfl

example {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (XP h j hj) ka wL wF) (S : WeightAlgebra.Scal (recB h.toLawsCore)) (a b : ℝ)
    (hT : G.TiedW S a b) : Generates h j hj S.sW G.w := hT.1

theorem ptNorm_nonneg (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) (p : FPt (T.U j σ).X) :
    0 ≤ ptNorm h j σ u F p :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg _ _ _)

theorem ptNorm_le_l2Norm (σ : T.Q.c.F →+* ℂ) {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → CuspAt h j wL)
    (p : FPt (T.U j σ).X) (i : Fin N) : ptNorm h j σ wL (w i) p ≤ l2Norm h j σ w p :=
  Real.le_sqrt_of_sq_le
    (Finset.single_le_sum (f := fun i => ptNorm h j σ wL (w i) p ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

example (σ : T.Q.c.F →+* ℂ) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) :
    supE (T.U j σ).X (laU (T.U j σ) (wtA u) u.n) (rdU (T.U j σ) (F.1 : T.R j)) =
      ⨆ p, ENNReal.ofReal (ptNorm h j σ u F p) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree
