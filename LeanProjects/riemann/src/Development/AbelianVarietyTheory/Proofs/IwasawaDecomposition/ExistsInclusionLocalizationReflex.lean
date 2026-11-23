import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlobalModelOfLocalModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersionStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models

namespace GlobalTheory.CoeffAway

theorem exists_isInc_away : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (a : ℕ), 0 < a → ∀ (ω : Localization.Away (a : 𝓞 c.F) →+* c.F), ω.comp (algebraMap (𝓞 c.F) (Localization.Away (a : 𝓞 c.F))) = algebraMap (𝓞 c.F) c.F → ∃ bR : RZ H a 1 →+* Localization.Away (a : 𝓞 c.F), IsInc (RZ H a 1).subtype (c.F.val.toRingHom.comp ω) bR := by
  intro E _ _ _ H l c a ha ω hω
  obtain ⟨b₀, hb₀⟩ := (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).2.2.1 1 (one_dvd _)
  obtain ⟨b₁, hb₁⟩ := (GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H 1 a 1 1 0 ha Nat.one_pos (one_dvd _) dvd_rfl).1
  letI := b₁.toAlgebra
  haveI := GlobalTheory.GlobalModel.isLocalization_away ha b₁ hb₁
  have hu : IsUnit (((algebraMap (𝓞 c.F) (Localization.Away (a : 𝓞 c.F))).comp b₀) (a : RZ H 1 1)) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a : 𝓞 c.F)) (a : 𝓞 c.F)
    rw [map_natCast] at h ⊢
    exact h
  refine ⟨IsLocalization.Away.lift (a : RZ H 1 1) hu, fun x => ?_⟩
  have key : ((c.F.val.toRingHom.comp ω).comp (IsLocalization.Away.lift (S := RZ H a 1) (a : RZ H 1 1) hu)) =
      (RZ H a 1).subtype := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (a : RZ H 1 1)) (RingHom.ext fun y => ?_)
    have h1 : (IsLocalization.Away.lift (S := RZ H a 1) (a : RZ H 1 1) hu) (algebraMap (RZ H 1 1) (RZ H a 1) y) =
        algebraMap (𝓞 c.F) (Localization.Away (a : 𝓞 c.F)) (b₀ y) := by
      simp [IsLocalization.Away.lift]
    have h2 : ω (algebraMap (𝓞 c.F) (Localization.Away (a : 𝓞 c.F)) (b₀ y)) = algebraMap (𝓞 c.F) c.F (b₀ y) :=
      congrArg (fun f => f (b₀ y)) hω
    simp only [RingHom.comp_apply, h1, h2]
    exact (hb₀ y).trans (hb₁ y).symm
  exact congrArg (fun f => f x) key

end GlobalTheory.CoeffAway
