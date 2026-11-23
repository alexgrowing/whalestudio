import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory

theorem exists_inverse_isogeny_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → Surjective Φ.left → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  intro hU hL K _ σ P P' Φ hg hΦ hs
  obtain ⟨hf, hfl, n, hn, hk⟩ := isogeny_of_surjective_polAV hU hL K σ P P' Φ hg hΦ hs
  have := P.isAb.comm
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 P.A ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 P.A ^ m) (𝟙 P.A) ≫ μ[P.A]))
  have hm := hpow n
  obtain ⟨⟨ψ, hψ, e⟩, hE⟩ := exists_monHom_factor_of_flat_surjective _ P.A P'.A P.A Φ (𝟙 P.A ^ n) hΦ hm hfl hs inferInstance
    (fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hk T x hx])
  refine ⟨n, ψ, hn, hψ, e, ?_⟩
  rw [← cancel_epi Φ, reassoc_of% e, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp,
    Category.comp_id]

end GlobalTheory
