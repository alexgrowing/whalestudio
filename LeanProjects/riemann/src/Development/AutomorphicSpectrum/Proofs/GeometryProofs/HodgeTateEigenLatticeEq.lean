import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOnDualAndBidual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li]
      [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n g : ℕ) (O : Type) [CommRing O]
      (ρ : O →+* Module.End Ω Li) (σ : O →+* Ω) (q : Cpt ξ), M.lat.IsVBOn {q} g ⊤ → M.htOm L n q = M.omLat q →
      M.htDual L n ρ σ q = M.eigLat ρ σ q ∧ ∀ 𝔡 : Ideal O, (∀ a, σ a ∈ regAt ξ q) →
        (∃ d ∈ 𝔡, unitAt ξ q (σ d)) → M.htW L n ρ σ 𝔡 q = M.eigLat ρ σ q := by
  intro X Ω _ ξ G _ Li _ _ M L n g O _ ρ σ q hVB hOm
  have hbi := (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat {q} g hVB).2 q rfl
  have hD : M.htDual L n ρ σ q = M.eigLat ρ σ q := by
    refine le_antisymm (fun e he => ?_) (M.eigLat_le_htDual L n ρ σ q)
    obtain ⟨he1, he2⟩ := (M.mem_htDual_iff L n ρ σ q e).1 he
    refine ⟨(hbi e).2 fun w hw => he2 w ?_, he1⟩
    rw [hOm]
    exact hw
  refine ⟨hD, fun 𝔡 hσ ⟨d, hd, hu, _, hinv⟩ => le_antisymm ?_ fun e he => ?_⟩
  · refine Submodule.span_le.2 fun e he => ?_
    have h1 : σ d • e ∈ M.eigLat ρ σ q := hD ▸ he.2 d hd
    have h2 : (⟨(σ d)⁻¹, hinv⟩ : regAt ξ q) • (σ d • e) ∈ M.eigLat ρ σ q := Submodule.smul_mem _ _ h1
    have h3 : (⟨(σ d)⁻¹, hinv⟩ : regAt ξ q) • (σ d • e) = e := by
      change (σ d)⁻¹ • (σ d • e) = e
      rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
    rwa [h3] at h2
  · refine Submodule.subset_span ⟨he.2, fun a ha => ?_⟩
    rw [hD]
    exact Submodule.smul_mem (M.eigLat ρ σ q) (⟨σ a, hσ a⟩ : regAt ξ q) he

end GlobalTheory.CompanionTheory.Ar
