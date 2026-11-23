import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthSetBddAboveOfUniqueCentre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starDepthSet_bddAbove_of_unique_centre : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → ∀ (n : ℕ) (π : (Fin n → O) →ₗ[O] X), Function.Surjective π → BddAbove (depthSet bar ψ w n (fun a b => B (π a) (π b))) := by
  first | exact @GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre | exact GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre | (intros; apply GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre <;> assumption)
