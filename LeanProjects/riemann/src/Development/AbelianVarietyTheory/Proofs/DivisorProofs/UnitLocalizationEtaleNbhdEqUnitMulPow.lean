import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitFormLocalizationEtaleNbhdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDivisorUnitDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqMulPowOnEtaleExcisionNbhdZeroLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeUnitEtaleExtension

namespace GlobalTheory.EtC

theorem kummer_divisor_step : ∀ (q : ℕ) (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∃ g : B, IsCoprime f g ∧ ∃ u : (Localization.Away (f * g))ˣ, (∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q) ∧ ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro q k B _ _ _ _ _ _ hq f hf A₂ _ _ hA c
  obtain ⟨b₁, m, e, he, hc⟩ := GlobalTheory.T.exists_unit_form_localization_etale_nbhd B A₂ f hA c
  by_cases hb : b₁ = 0
  · refine ⟨1, isCoprime_one_right, 1, ?_, ⟨B, inferInstance, inferInstance, isExcisionNbhd_self B 1, 1, by simp⟩⟩
    have hL := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA e 1 (by simpa using he)
    refine ⟨Localization.Away e, inferInstance, inferInstance, inferInstance, inferInstance, hL, by simp, 1, ?_⟩
    intro φ ψ hφ hψ
    subst hb
    have hc' := congrArg φ hc
    simp only [map_zero, map_mul, map_pow] at hc'
    have hx : IsUnit (φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) e) *
        φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ f)) ^ m) := by
      have h1 : ∀ y : A₂, φ (algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) y) =
          algebraMap (Localization.Away e) _ (algebraMap A₂ (Localization.Away e) y) := fun y => by
        rw [← RingHom.comp_apply, hφ]; rfl
      rw [h1, h1]
      refine IsUnit.mul ((IsLocalization.Away.algebraMap_isUnit e).map _) (IsUnit.pow _ ?_)
      rw [← IsScalarTower.algebraMap_apply]
      exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap B (Localization.Away e) f)) (algebraMap B (Localization.Away e) f)
    have hu := (c.isUnit.map φ).mul hx
    rw [← hc'] at hu
    haveI := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)
    exact Subsingleton.elim _ _
  · obtain ⟨g, hg0, hfg, u, n, d, t, n', d', hn, hd, hn', hd', h1, h2⟩ := GlobalTheory.T.smoothAffineCurve_divisor_unit_decomposition k B q hq f hf b₁ hb m
    exact ⟨g, hfg, u, GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus k B q hq f hf A₂ hA c b₁ m e he hc g hfg u n d hn hd h1,
      GlobalTheory.T.coprime_unit_etale_extension k B q hq f g hg0 u t n' d' hn' hd' h2⟩

end GlobalTheory.EtC
