import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def lamOf (la : HeightOneSpectrum (𝓞 c.F)) : PointsOfFlagModel.abelian₂ (Formalism.MainNotions.WeightAlgebra.resCh la) c :=
  ⟨la, by
    have h : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : 𝓞 c.F ⧸ la.asIdeal) = 0 := by
      unfold Formalism.MainNotions.WeightAlgebra.resCh
      exact CharP.cast_eq_zero _ _
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa using h)⟩

def LiesOverBaseChange (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (η : PointsOfFlagModel.Pt Tw .yy) : Prop :=
  letI := io.toAlgebra
  η.1 = lamOf la ∧ ∃ eF : T.Fr →+* ↥η.2.1.S,
    eF.comp io = η.2.2.1.fK ∧
    (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧
    (∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧
    η.2.2.1.y ≫ pullback.fst _ _ = spMap eF ≫ y.1.x ∧
    ∀ τ i, ∃ u' : Sp (DualNumber ↥η.2.1.S) ⟶ (Tw.Y η.1).oF.t.G.left,
      u' ≫ (Tw.Y η.1).m.φ = (η.2.2.2.u τ i).left ∧
      u' ≫ (Tw.Y η.1).m0.toSABMap.φ = spMap (dualMap eF) ≫ y.1.u τ i

end Formalism.L2.Pj
