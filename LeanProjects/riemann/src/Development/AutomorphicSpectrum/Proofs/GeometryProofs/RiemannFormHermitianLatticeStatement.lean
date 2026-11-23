import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RiemannFormHermitianLattice
import Mathlib
open Filter Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_hermitian_lattice : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (τ G : Matrix (Fin g) (Fin g) ℂ) (c : ℝ), 0 < c → (Bs.map (fun x : ℤ => (x : ℝ))).PosSemidef → τᵀ = τ → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((τ.map Complex.im) *ᵥ v)) → G.IsHermitian → (∀ u u' v v' : Fin g → ℤ, Bs *ᵥ v = 0 → Bs *ᵥ v' = 0 → (((fun k => (u k : ℂ)) + τ *ᵥ (fun k => (v k : ℂ))) ⬝ᵥ G *ᵥ star ((fun k => (u' k : ℂ)) + τ *ᵥ (fun k => (v' k : ℂ)))).im = ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ)) → (∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) → G *ᵥ (fun k => (u k : ℂ)) = 0) → ∀ y : Fin g → ℂ, 0 ≤ (y ⬝ᵥ G *ᵥ star y).re ∧ (y ⬝ᵥ G *ᵥ star y).re ≤ c⁻¹ * ∑ i, ‖y i‖ ^ 2 ∧ ((y ⬝ᵥ G *ᵥ star y).re = 0 → y ∈ Submodule.span ℂ {p : Fin g → ℂ | ∃ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) ∧ p = fun k => (u k : ℂ)}) := by
  first | exact @GlobalTheory.CompanionTheory.RiemannForm.form_bounds | exact GlobalTheory.CompanionTheory.RiemannForm.form_bounds | (intros; apply GlobalTheory.CompanionTheory.RiemannForm.form_bounds <;> assumption)
