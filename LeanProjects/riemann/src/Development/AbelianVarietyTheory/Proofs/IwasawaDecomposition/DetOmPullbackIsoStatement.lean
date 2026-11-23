import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetOmPullbackIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detOm_pullback_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Nonempty (SABMap Z.t X.t π) → (GlobalTheory.FlagMod.detOm X).IsLB → (GlobalTheory.FlagMod.detOm Z).IsLB ∧ LBIso (GlobalTheory.FlagMod.detOm Z) ((GlobalTheory.FlagMod.detOm X).pull π) := by
  first | exact @GlobalTheory.DetOmPull.detOm_pull | exact GlobalTheory.DetOmPull.detOm_pull | (intros; apply GlobalTheory.DetOmPull.detOm_pull <;> assumption)
