import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthSetBddAboveOfUniqueCentreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStarDepthSetThroughRadicalFreePresentationStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem depth_le_starDepth : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X) (t : ℝ), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → 0 ≤ t → B - t • toReal v ∈ rcone γ → t ≤ evalR (starDepth bar ψ w) B := by
  intro O _ bar ψ w X _ _ _ m γ B v t hγ hB hv hvp hvw hvc hv0 huniq ht hBt
  rcases ht.eq_or_lt with rfl | ht
  · exact starDepth_eval_nonneg _
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O X
  show t ≤ (starDepth bar ψ w).eval X (fun a b => B a b)
  rw [InvFun.eval_eq _ hπ]
  exact le_csSup (GlobalTheory.T.starDepthSet_bddAbove_of_unique_centre O bar ψ w X m γ B v hγ hB hv hvp hv0 huniq n π hπ)
    (GlobalTheory.T.mem_starDepthSet_through_radicalFree_presentation O bar ψ w X m γ B v t hγ hB hv hvp hvw hvc ht hBt n π hπ)

end GlobalTheory.PolFan
