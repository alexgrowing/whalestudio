import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem scale_pull_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (W : Submodule Ω V) (W' : Submodule Ω' V') (O : Type) [CommRing O] (σ : O →+* Ω) (𝔡 : Ideal O) (d₀ : O) (D : Submodule R V) (D' : Submodule R' V'), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → W' = Submodule.span Ω' (j '' (W : Set V)) → d₀ ∈ 𝔡 → σ d₀ ≠ 0 → (∀ d ∈ 𝔡, σ d / σ d₀ ∈ R) → (∀ e ∈ D, e ∈ W) → D' = Submodule.span R' (j '' (D : Set V)) → Submodule.span R' {e | e ∈ W' ∧ ∀ d ∈ 𝔡, (i.comp σ) d • e ∈ D'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
  intro Ω Ω' _ _ i R R' V V' _ _ _ _ j W W' O _ σ 𝔡 d₀ D D' hsemi hR hW' hd₀ hσd₀ hdiv hDW hD'
  have hj : ∀ (a : Ω) (v : V), j (a • v) = i a • j v := hsemi.1
  subst hW' hD'
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro e ⟨-, he⟩
    have hu : i (σ d₀) ≠ 0 := (map_ne_zero i).mpr hσd₀
    have key : ∀ y ∈ Submodule.span R' (j '' (D : Set V)),
        (i (σ d₀))⁻¹ • y ∈ Submodule.span R'
          (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨(σ d₀)⁻¹ • x, Submodule.subset_span ⟨W.smul_mem (σ d₀)⁻¹ (hDW x hx), fun d hd => ?_⟩, ?_⟩
        · rw [smul_smul, ← div_eq_mul_inv]
          exact D.smul_mem ⟨σ d / σ d₀, hdiv d hd⟩ hx
        · rw [hj, map_inv₀]
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul a y _ hy =>
        have e1 : (i (σ d₀))⁻¹ • (a • y) = a • ((i (σ d₀))⁻¹ • y) :=
          show (i (σ d₀))⁻¹ • ((a : Ω') • y) = (a : Ω') • ((i (σ d₀))⁻¹ • y) by
            rw [smul_smul, smul_smul, mul_comm]
        rw [e1]
        exact Submodule.smul_mem _ a hy
    have h1 := key _ (he d₀ hd₀)
    rwa [RingHom.comp_apply, inv_smul_smul₀ hu] at h1
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv =>
      apply Submodule.subset_span
      refine ⟨Submodule.subset_span ⟨v, hv.1, rfl⟩, fun d hd => ?_⟩
      rw [RingHom.comp_apply, ← hj]
      exact Submodule.subset_span ⟨_, hv.2 d hd, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      show j ((a : Ω) • x) ∈ _
      rw [hj]
      exact Submodule.smul_mem _ ⟨i a, hR a a.2⟩ hx

end GlobalTheory.CompanionTheory.Ar
