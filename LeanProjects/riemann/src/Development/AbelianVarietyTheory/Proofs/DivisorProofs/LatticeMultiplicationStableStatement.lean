import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMultiplicationStable
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_multiplication_stable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (𝔠 : FracId F) (r : Fin (Module.finrank ℚ F) → ℝ) (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)),
    (∀ i, 0 < r i) → DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin (Module.finrank ℚ F) → ℂ)) = ⊤ →
    (∀ (a : 𝓞 F), ∀ w ∈ Λ, (fun i ↦ (e i (a : F) : ℂ) * w i) ∈ Λ) →
    (∀ c ∈ 𝔠.elt, ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e i c * r i : ℝ) : ℂ) * l i * starRingEnd ℂ (l' i)).im = n) →
    (∀ w : Fin (Module.finrank ℚ F) → ℂ, (∀ c ∈ 𝔠.elt, ∀ l ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e i c * r i : ℝ) : ℂ) * w i * starRingEnd ℂ (l i)).im = n) → w ∈ Λ) →
    ∀ c : 𝔠.elt, IsTotPos (c : F) →
    ∃ (X : Obj F 𝔠 (Sp ℂ)) (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)),
      (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧
      (∀ (a : 𝓞 F) w, u.ex (fun i ↦ (e i (a : F) : ℂ) * w i) = u.ex w ≫ X.rm.act a) ∧
      ∃ χ, u.IsAH (Matrix.diagonal fun i ↦ ((2 * (e i (c : F) * r i) : ℝ) : ℂ)) χ := by
  first | exact @GlobalTheory.TorusRM.exists_obj_of_polarised_torus | exact GlobalTheory.TorusRM.exists_obj_of_polarised_torus | (intros; apply GlobalTheory.TorusRM.exists_obj_of_polarised_torus <;> assumption)
