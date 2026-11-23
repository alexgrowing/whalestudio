import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChristoffelTransferBiholomorphic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
open Filter Topology Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.christoffel_transfer_biholomorphic : ∀ (d : ℕ) (U U' : Set (ReciprocityTheory.L2DbarEstimates.V d)) (τ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (b b' : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ), IsOpen U → IsOpen U' → DifferentiableOn ℂ τ U → Set.MapsTo τ U U' → (∀ n, ContDiffOn ℝ ∞ (GlobalTheory.ChernReg.jet b' n) (U' ×ˢ (Set.univ : Set (ReciprocityTheory.L2DbarEstimates.V d)))) → (∀ z ∈ U, ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, fderiv ℂ τ z (GlobalTheory.ChernReg.christoffel b z ξ) = GlobalTheory.ChernReg.christoffel b' (τ z) (fderiv ℂ τ z ξ) + fderiv ℂ (fderiv ℂ τ) z ξ ξ) → ∀ (n : ℕ), ∀ q ∈ U ×ˢ (Set.univ : Set (ReciprocityTheory.L2DbarEstimates.V d)), (GlobalTheory.ChernReg.holSpray b)^[n] (τ ∘ Prod.fst) q = GlobalTheory.ChernReg.jet b' n (τ q.1, fderiv ℂ τ q.1 q.2) := by
  first | exact @GlobalTheory.ChernReg.holSpray_iterate_comp | exact GlobalTheory.ChernReg.holSpray_iterate_comp | (intros; apply GlobalTheory.ChernReg.holSpray_iterate_comp <;> assumption)
