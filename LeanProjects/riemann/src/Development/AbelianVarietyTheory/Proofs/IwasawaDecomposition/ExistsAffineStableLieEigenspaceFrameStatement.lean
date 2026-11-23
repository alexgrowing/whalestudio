import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (z : gen Z), ∃ (U : (gen Z).Opens) (hU : IsAffineOpen U) (φ : c.F →+* Γ(gen Z, U)) (f : EigFrame Z φ (hU.fromSpec ≫ genι Z)), z ∈ U ∧ hU.fromSpec ≫ genStr Z = spMap φ ∧ f.Stable := by
  first | exact @GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame | exact GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame | (intros; apply GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame <;> assumption)
