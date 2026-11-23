import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuperadditiveOfCellsCoverConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAutStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarFan

theorem homog_of_cover : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) → ∀ B ∈ psdCone bar X, ∀ t : ℝ, 0 ≤ t → evalR φ (t • B) = t * evalR φ B := by
  intro O _ bar φ X _ _ _ hcov B hB t ht
  obtain ⟨e, m, γ, c, hγ, hc, he⟩ := hcov B hB
  have key : ∀ (B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (c₀ : Fin m → ℝ), (∀ i, 0 ≤ c₀ i) →
      (∀ a b, B₀ (e a) (e b) = ∑ i, c₀ i * (γ i a b : ℝ)) → evalR φ B₀ = ∑ i, c₀ i * φ.evalZ (γ i) :=
    fun B₀ c₀ hc₀ hB₀ => hγ.linear.eval_eq_sum (r := e.toLinearMap) e.surjective hc₀ hB₀
  have hv : ∀ a b, B (e a) (e b) = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    have := LinearMap.congr_fun₂ he a b
    simpa [LinearMap.sum_apply] using this
  rw [key B c hc hv, key (t • B) (fun i => t * c i) (fun i => mul_nonneg ht (hc i)) fun a b => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isPolyFan_star : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, ψ'.evalZ β = n) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ψ'.evalZ β) → IsPolyFan H.bar q ψ' := by
  intro E _ _ _ H q ψ w ψ' hψ hw hst hint hpos X _ _ _ _ hX
  obtain ⟨S, hS, hcov⟩ := GlobalTheory.T.starSubdivision_cells_finite_cover_up_to_aut E H q ψ w ψ' hψ hw hst X hX
  have hcov' : ∀ B ∈ psdCone H.bar X, ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsCell H.bar ψ' γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := fun B hB => by
    obtain ⟨e, m, γ, c, h1, -, h3, h4⟩ := hcov B hB
    exact ⟨e, m, γ, c, h1, h3, h4⟩
  exact
    { homog := homog_of_cover (𝓞 E) H.bar ψ' X hcov'
      superadd := GlobalTheory.T.superadditive_of_cells_cover_cone (𝓞 E) H.bar ψ' X hcov'
      integral := hint X hX
      pos := hpos X hX
      finite := ⟨S, hS, hcov⟩ }

end GlobalTheory.PolFan.StarFan
