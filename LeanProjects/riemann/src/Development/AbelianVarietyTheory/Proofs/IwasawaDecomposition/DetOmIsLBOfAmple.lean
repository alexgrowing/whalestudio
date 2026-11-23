import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PolDet

theorem isLB_detOm_of_ample : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (m : ℕ) (BD : GlobalTheory.EffCartierData Y.X), GlobalTheory.IsAmpleLB (polOf Y m BD) → (GlobalTheory.FlagMod.detOm Y).IsLB := by
  intro E _ _ _ H D l Xo c O _ β Y m BD h
  exact GlobalTheory.CechPic.isLB_dual (GlobalTheory.PolFin.isLB_detLie_of_polOf h.isLB)

end GlobalTheory.PolDet
