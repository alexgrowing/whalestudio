import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPotentialTransportHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotential_transport_homeomorph : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : LocPot X), IsPotential A P → IsPotential (tAtlas A h) (P.pullback h.symm h.symm.continuous) := by
  first | exact @GlobalTheory.Adopt.isPotential_transport_homeomorph | exact GlobalTheory.Adopt.isPotential_transport_homeomorph | (intros; apply GlobalTheory.Adopt.isPotential_transport_homeomorph <;> assumption)
