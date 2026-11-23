import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeodesicJetHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
open Filter Topology Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geodesic_jet_holomorphic : ∀ (d : ℕ) (U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (b : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ) (g : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d), IsOpen U → (∀ n, ContDiffOn ℝ ∞ (GlobalTheory.ChernReg.jet b n) (U ×ˢ (Set.univ : Set (ReciprocityTheory.L2DbarEstimates.V d)))) → DifferentiableOn ℂ g U → ∀ z ∈ U, ∀ (ξ : ReciprocityTheory.L2DbarEstimates.V d) (u : ℝ → ReciprocityTheory.L2DbarEstimates.V d), ContDiffAt ℝ ∞ u 0 → (∀ n, iteratedDeriv n u 0 = GlobalTheory.ChernReg.jet b n (z, ξ)) → ∀ (n : ℕ), iteratedDeriv n (g ∘ u) 0 = (GlobalTheory.ChernReg.holSpray b)^[n] (g ∘ Prod.fst) (z, ξ) := by
  first | exact @GlobalTheory.ChernReg.iteratedDeriv_comp_eq_iterate_holSpray | exact GlobalTheory.ChernReg.iteratedDeriv_comp_eq_iterate_holSpray | (intros; apply GlobalTheory.ChernReg.iteratedDeriv_comp_eq_iterate_holSpray <;> assumption)
