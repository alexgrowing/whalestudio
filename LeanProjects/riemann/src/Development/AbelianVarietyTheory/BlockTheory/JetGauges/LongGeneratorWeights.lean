import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LongGeneratorWeights

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

variable {D : D7}

def NeZeroOn (T : Top D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp) (f : T.R j) : Prop :=
  ∃ x : ((T.U j σ).X k).dom, toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k x)) ≠ 0

def ThetaWt (D : D7) {j : ℕ} (w : WeightFamilies.Wt D j) : Prop :=
  D.R.r ≤ w.n ∧
  w.LastPos ∧
  4 * WeightAlgebra.DF w + 4 ≤ D.host.g 0 * D.host.g 1

def l1At {K ι : Type} [Field K] (σ : K →+* ℂ) (P : MvPolynomial ι K) : ℝ :=
  ∑ m ∈ P.support, ‖σ (P.coeff m)‖

def shortBound (D : D7) {j : ℕ} (w : WeightFamilies.Wt D j) : ℝ :=
  ((w.n : ℝ) * WeightAlgebra.DF w * D.R.f * Real.exp (WeightAlgebra.lrd D)) ^ (20 * D.R.r * WeightAlgebra.DF w)

def IsShortPoly (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) : Prop :=
  P ∈ harmA (Dw := T.Q.Dw j) T.Q.c (wtA w) w.n ∧ ∀ σ : T.Q.c.F →+* ℂ, l1At σ P ≤ shortBound D w

def IsLongGen (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (f : T.R j) : Prop :=
  ∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    IsShortPoly T j w P ∧ IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f

def NonZeroDivisor {T : Top D} (h : LawsP T) : Prop :=
  ∀ (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w) (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → (∀ k, NeZeroOn T j σ k F.1) → (recPJ h j hj).NonZeroComp w F

def NoBasePoint (T : Top D) : Prop :=
  ∀ (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, ThetaWt D w →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp,
      ∃ f ∈ T.C j w, IsLongGen T j w f ∧ NeZeroOn T j σ k f

def ThetaWeightsFromLaws {T : Top D} (h : LawsP T) : Prop :=
  ∀ (large₂ : SizeData₂ D) (H : WeightAlgebra.KHyp) (C2 A2 CR CT : ℝ) (j : ℕ) (hj : InR D j) (ka wL wF : WeightFamilies.Wt D j)
    (T₀ nP nW : ℕ) (h0 : ℝ),
    Gaps.FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF T₀ nP nW h0 →
      (∃ w2 : WeightFamilies.Wt D j, WeightAlgebra.IsG2 wL wF w2 ∧ ThetaWt D w2) ∧
      (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, WeightAlgebra.IsDoubledWeightWithShift wL w1 nW ∧ ThetaWt D w1)

def Leaves : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T), NonZeroDivisor h ∧ NoBasePoint T ∧ ThetaWeightsFromLaws h

end GlobalTheory.IndefiniteRowSideFullHecke.LongGeneratorWeights
