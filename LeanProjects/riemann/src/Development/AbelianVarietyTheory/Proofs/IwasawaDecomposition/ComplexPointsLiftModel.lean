import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory

theorem ringOfIntegers_hom_complex_injective (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem model_cxPts_from_generic_fibre :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (τ : 𝓞 F →+* ℂ) (y' : CxPts M.p τ),
      ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ ∧ ∃ y : Pts Y σ, y'.1 = y.1 ≫ M.j := by
  intro F _ _ Y M τ y'
  have hτ := ringOfIntegers_hom_complex_injective F τ
  obtain ⟨σ, hσ⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ :=
    ⟨IsFractionRing.lift (K := F) hτ, RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) hτ x⟩
  refine ⟨σ, hσ, ?_⟩
  have hw : y'.1 ≫ M.p = spMap σ ≫ spMap (algebraMap (𝓞 F) F) :=
    y'.2.trans ((congrArg spMap hσ.symm).trans (spMap_comp _ _))
  exact ⟨⟨M.pb.lift y'.1 _ hw, M.pb.lift_snd _ _ _⟩, (M.pb.lift_fst _ _ _).symm⟩

end GlobalTheory
