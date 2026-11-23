import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendedRaysMarkedFormPieces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullAddInjective
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_rays_marked_form_pieces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]
  [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (hm : ∀ i, δ₀ i ∈ balForms H.bar X₀),
  (∀ i y, 0 ≤ δ₀ i y y) → LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, hm i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X) (τ : 𝓞 E ≃+* 𝓞 E)
    (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)), τ H.w0 = H.w0 → Function.Surjective f →
    (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
    (∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀) →
  ∃ u : Fin m₀ → LinearMap.BilinForm ℤ (X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)),
    toReal β = ∑ i, t i • toReal (pullAdd f (u i)) ∧
    LinearIndependent ℤ (fun i : {i // 0 < t i} => pullAdd f (u i)) ∧
    ∀ i, 0 < t i → pull (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧
      (∀ y, 0 ≤ pullAdd f (u i) y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = pullAdd f (u i) → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (pullAdd f (u i)) = lab.evalZ (δ₀ i) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd | exact GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd | (intros; apply GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd <;> assumption)
