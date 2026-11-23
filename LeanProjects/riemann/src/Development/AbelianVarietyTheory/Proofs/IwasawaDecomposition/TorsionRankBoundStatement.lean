import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRankBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_rank_bound : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → P.TorsionIso → Module.finrank ℤ P.D.toPre.X ≤ Module.finrank ℚ E * min D.p D.q := by
  first | exact @GlobalTheory.CharRankZ.finrank_int_le_min | exact GlobalTheory.CharRankZ.finrank_int_le_min | (intros; apply GlobalTheory.CharRankZ.finrank_int_le_min <;> assumption)
