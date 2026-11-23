import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBundleInvertibleSectionsLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_bundle_invertible_sections_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X), Y.jQ ≫ ρ = X.jQ →
    (GlobalTheory.FlagMod.detOm Y).IsLB → ∀ y : gen Y, ∃ U : (gen X).affineOpens, ρ y ∈ U.1 ∧
      ∃ e ∈ secOn ((GlobalTheory.FlagMod.detOm Y).pull (genι Y)) (ρ ⁻¹ᵁ U.1), ∀ i, IsUnit (e i) := by
  first | exact @GlobalTheory.GenFrame.detOm_frame_gen | exact GlobalTheory.GenFrame.detOm_frame_gen | (intros; apply GlobalTheory.GenFrame.detOm_frame_gen <;> assumption)
