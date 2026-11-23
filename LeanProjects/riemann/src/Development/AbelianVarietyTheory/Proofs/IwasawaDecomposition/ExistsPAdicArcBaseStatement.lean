import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_p_adic_arc_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O' : Type)
    [CommRing O'] [IsDomain O'] [CharZero O'] (b : 𝓞 c.F →+* O') (ϖ : O'), IsArcBase O' ϖ →
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (bV : 𝓞 c.F →+* c.V W)
      (b' : c.V W →+* O'), (∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) ∧ b'.comp bV = b := by
  first | exact @GlobalTheory.ArcBaseFactor.factor | exact GlobalTheory.ArcBaseFactor.factor | (intros; apply GlobalTheory.ArcBaseFactor.factor <;> assumption)
