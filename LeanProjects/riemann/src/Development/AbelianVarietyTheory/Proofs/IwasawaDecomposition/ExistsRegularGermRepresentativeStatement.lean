import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRegularGermRepresentative
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_germ_representative : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (z : Z.X) (a : Z.X.presheaf.stalk z), a ≠ 0 → ∃ (U : Z.X.Opens) (hz : z ∈ U) (f : Γ(Z.X, U)), (Z.X.presheaf.germ U z hz).hom f = a ∧ IsRegularFn f := by
  first | exact @GlobalTheory.GermSpread.exists_isRegularFn_germ_eq | exact GlobalTheory.GermSpread.exists_isRegularFn_germ_eq | (intros; apply GlobalTheory.GermSpread.exists_isRegularFn_germ_eq <;> assumption)
