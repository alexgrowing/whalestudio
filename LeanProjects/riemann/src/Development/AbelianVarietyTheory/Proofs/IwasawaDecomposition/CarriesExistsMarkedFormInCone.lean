import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem carries_exists_marked : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  intro O _ bar w0 c X₀ _ _ _ m δ₀ v t hbal hv hpos hc₀ ht hsum X _ _ _ m' δ hc
  obtain ⟨e₀, s₀, hδ₀⟩ := hc₀
  obtain ⟨e, s, hδ⟩ := hc
  set g : X ≃ₗ[O] X₀ := e.trans e₀.symm with hg
  refine ⟨pull g.toLinearMap v, pull_mem _ hbal, fun y => by simpa using hpos (g y), ?_, ?_⟩
  · rw [evalZ_pull _ g.surjective]
    exact OrbMark.orbFun_evalZ_self w0 hv hbal.1
  · refine ⟨fun j => t (s₀.symm (s j)), fun j => ht _, LinearMap.ext₂ fun a b => ?_⟩
    have h1 := LinearMap.congr_fun₂ hsum (g a) (g b)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at h1 ⊢
    show ((v (g a) (g b) : ℤ) : ℝ) = _
    rw [h1]
    have key : ∀ i, (δ₀ i (g a) (g b) : ℝ) = (c.δ (s₀ i) (e a) (e b) : ℝ) := fun i => by
      rw [hδ₀ i, pull_apply]; simp [hg]
    have key' : ∀ j, (δ j a b : ℝ) = (c.δ (s j) (e a) (e b) : ℝ) := fun j => by
      rw [hδ j, pull_apply]; rfl
    simp only [key, key']
    rw [← (s.trans s₀.symm).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp

end GlobalTheory.PolFan
