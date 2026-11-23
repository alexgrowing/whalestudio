import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def NZDOfCompSt : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    (∀ k, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) (F.1 : T.R j) k x ≠ 0) →
    (recPJ h j hj).NonZeroComp w F

def NoBaseSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → DF w + 2 ≤ qq D →
    (∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}) →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k,
      ∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (f : T.R j),
        P ∈ harmA T.Q.c (wtA w) w.n ∧
        (∀ σ' : T.Q.c.F →+* ℂ, Real.log (∑ m ∈ P.support, ‖σ' (P.coeff m)‖) ≤ 140 * D.R.r * large₂.sc.L * absA w) ∧
        IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f ∧ ∃ x' ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) f k x' ≠ 0

def ThetaWeightBounds : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (j : ℕ) (hj : InR D j)
    (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    Formalism.MainNotions.Gaps.FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 →
    (∀ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 →
      D.R.r ≤ w2.n ∧ LastPos (T.Q.Dw j) (wtA w2) ∧ DF w2 + 2 ≤ qq D) ∧
    (j < D.R.m → ∀ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW →
      D.R.r ≤ w1.n ∧ LastPos (T.Q.Dw j) (wtA w1) ∧ DF w1 + 2 ≤ qq D)

def SupGenSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) →
    ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      Real.log (∑ m ∈ P.support, ‖σ (P.coeff m)‖) ≤ 140 * D.R.r * large₂.sc.L * absA w + 4 * D.R.f * D.R.r * w.n * large₂.sc.L →
      Real.log (T.Ns j w σ f) ≤
        (140 * D.R.r + 4) * large₂.sc.L * absA w + 67 * D.R.f * D.R.r * w.n * large₂.sc.L

end ReciprocityTheory.ChartRestriction.G.PullbackSections
