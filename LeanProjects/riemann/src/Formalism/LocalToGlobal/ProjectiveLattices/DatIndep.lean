import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def NabUniq : Prop :=
  ∀ (_ : StarRing (𝓞 E)) (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ a n, Dom a n → thGen Xo c nab a n = thGen Xo c nab' a n

def DatIndep : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Tw Tw' : PointsOfFlagModel.Tower (WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → PointsOfFlagModel.TowerAt Tw' →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io), OverLa la T.V io e → algCls Xo c T io y →
      ∀ z z', LiesOverBaseChange la Tw T io y z → LiesOverBaseChange la Tw' T io y z' →
        ∀ (A : DatAt (Tw.Y z.1) z.2.2.1) (A' : DatAt (Tw'.Y z'.1) z'.2.2.1),
          ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b

end Formalism.L2.Pj
