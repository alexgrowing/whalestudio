import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

variable {D : D7}

def aAbs {j : ℕ} (w : WeightFamilies.Wt D j) : ℕ :=
  ∑ τ, ((∑ i, w.aP τ i) + ∑ i, w.aM τ i)

def aDeg (T : Core D) {j : ℕ} (w : WeightFamilies.Wt D j) : ℕ :=
  ∑ τ : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult τ), wtA w (τ, i)

def PolyFrStatement (T : Core D) : Prop :=
  LawsCore T → ∀ (j : ℕ), InR D j → AllTest (T.Q.Xo j) T.Q.c → ∀ (w : WeightFamilies.Wt D j) (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁]
    (d : ArcDatumAt T j K₁) (F : T.R j), F ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n →
    ∃ P : MvPolynomial (ArcLt (T.Q.Dw j)) (LaurentSeries K₁),
      algebraMap _ (ArcS (T.Q.Dw j) K₁) P = evR (T.Q.Xo j) T.Q.c F d.yF ∧ P.IsHomogeneous (aDeg T w)

end Formalism.L2.Pj.QAt
