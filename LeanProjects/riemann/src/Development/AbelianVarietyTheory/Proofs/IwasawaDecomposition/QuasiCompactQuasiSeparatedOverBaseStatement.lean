import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuasiCompactQuasiSeparatedOverBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiCompact_quasiSeparated_over_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), π ≫ X.s = Z.s → QuasiCompact π ∧ QuasiSeparated π := by
  first | exact @GlobalTheory.GModMap.quasiCompact_quasiSeparated | exact GlobalTheory.GModMap.quasiCompact_quasiSeparated | (intros; apply GlobalTheory.GModMap.quasiCompact_quasiSeparated <;> assumption)
