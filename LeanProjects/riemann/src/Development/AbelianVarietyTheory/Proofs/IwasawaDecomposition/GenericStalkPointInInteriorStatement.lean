import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericStalkPointInInterior
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_stalk_point_in_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X) (p : PrimeSpectrum (Z.X.presheaf.stalk z)), p.asIdeal = ⊥ → Z.X.fromSpecStalk z p ∈ Set.range Z.j := by
  first | exact @GlobalTheory.TorRef.fromSpecStalk_bot_mem_range_j | exact GlobalTheory.TorRef.fromSpecStalk_bot_mem_range_j | (intros; apply GlobalTheory.TorRef.fromSpecStalk_bot_mem_range_j <;> assumption)
