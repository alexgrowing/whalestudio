import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEigenFrameLocal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_eigen_frame_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}, Smooth (genStr Z) → ∀ z : gen Z, ∃ (V : (gen Z).Opens) (hV : IsAffineOpen V) (φV : c.F →+* Γ(gen Z, V)) (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), z ∈ V ∧ IsIntegral V.toScheme ∧ hV.fromSpec ≫ genStr Z = spMap φV := by
  first | exact @GlobalTheory.ShFam.IntCell.exists_integral_eigFrame | exact GlobalTheory.ShFam.IntCell.exists_integral_eigFrame | (intros; apply GlobalTheory.ShFam.IntCell.exists_integral_eigFrame <;> assumption)
