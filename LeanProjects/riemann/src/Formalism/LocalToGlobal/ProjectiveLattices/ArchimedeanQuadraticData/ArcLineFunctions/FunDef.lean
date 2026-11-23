import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

noncomputable def arcNum {K₁ : Type} [Field K₁] (s : ArcS Dw K₁) :
    MvPolynomial (ArcLt Dw) (LaurentSeries K₁) := by
  classical
  exact if h : ∃ P, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) P = s
    then h.choose else 0

variable {Xo : Moduli Dw l} {c : Coeff l}

noncomputable def cfOf {K₁ : Type} [Field K₁] [Algebra c.F (ArcS Dw K₁)]
    (yF : FrPt Xo c (ArcS Dw K₁)) (μ : ArcLt Dw →₀ ℕ) (j : ℤ) (F : Rul Xo c) : K₁ :=
  (MvPolynomial.coeff μ (arcNum (evR Xo c F yF))).coeff j

end Formalism.L2.Pj.QAt
