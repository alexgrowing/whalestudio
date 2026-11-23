import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SaturatedCokernelVectorBundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturated_cokernel_vector_bundle : ∀ (C : Scheme.{0}) [IsIntegral C] [IsLocallyNoetherian C] (F G : C.Modules) (r : ℕ) (φ : G ⟶ F), IsVB F (r + 1) → IsVB G 1 → Mono φ → (∀ x : C, IsPrincipalIdealRing (C.presheaf.stalk x) ∨ ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :), ρ ∘ₗ GlobalTheory.QCoh.stalkLinear φ x = LinearMap.id) → IsVB (Limits.cokernel (satι φ)) r := by
  first | exact @GlobalTheory.VB.isVB_cokernel_satι_of_split | exact GlobalTheory.VB.isVB_cokernel_satι_of_split | (intros; apply GlobalTheory.VB.isVB_cokernel_satι_of_split <;> assumption)
