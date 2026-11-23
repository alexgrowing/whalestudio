import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseImageBoundaryPower
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_image_boundary_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (ρ : gen Y ⟶ gen X) (n : ℕ),
    Y.jQ ≫ ρ = X.jQ → ρ ⁻¹' Set.range X.jQ = Set.range Y.jQ → (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) →
    Dense (((((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support : Set X.X)ᶜ) := by
  first | exact @GlobalTheory.BlowSupp.dense_compl_support_map | exact GlobalTheory.BlowSupp.dense_compl_support_map | (intros; apply GlobalTheory.BlowSupp.dense_compl_support_map <;> assumption)
