import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceNotIsSquareAdicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFacts
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquare
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_place_isSquare_and_not_isSquare :
    ∀ (F : Type) [Field F] [NumberField F] (δ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → u ≠ 0 → ¬ IsSquare δ → ¬ IsSquare u → ¬ IsSquare (u * δ) → ∃ v, v ∉ S₀ ∧ IsSquare (algebraMap F (v.adicCompletion F) δ) ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  classical
  intro F _ _ δ u S₀ hδ hu hδs hus huδs
  obtain ⟨E, _, _, _, θ, σ, hq⟩ := exists_isQuad F δ hδs
  have hbasic := isQuad_basic F E δ θ σ hq
  have huE : ¬ IsSquare (algebraMap F E u) := fun h => (hbasic.2.2.2.2.2.1 u h).elim hus huδs
  have hu0E : algebraMap F E u ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr hu
  obtain ⟨S, hS₀, hSunits⟩ := exists_superset_mem_sUnits F
    {Units.mk0 (2 : F) two_ne_zero, Units.mk0 u hu, Units.mk0 (u * δ) (mul_ne_zero hu hδ)} S₀
  have hgood : ∀ v, v ∉ S → ∀ x ∈ ({Units.mk0 (2 : F) two_ne_zero, Units.mk0 u hu,
      Units.mk0 (u * δ) (mul_ne_zero hu hδ)} : Finset Fˣ), v.valuation F (x : F) = 1 :=
    fun v hv x hx => (mem_sUnits F S x).mp (hSunits S subset_rfl x hx) v hv
  obtain ⟨hover, -, -⟩ := places_over F E
  obtain ⟨SE, hSE⟩ := hover S
  obtain ⟨w, hwS, hwu⟩ := GlobalTheory.T.exists_place_not_isSquare_adicCompletion E (algebraMap F E u) SE hu0E huE
  have hvS : w.under (𝓞 F) ∉ S := fun h => hwS ((hSE w).mpr h)
  obtain ⟨φ, hφ⟩ := exists_ringHom_adicCompletion_under F E w
  have hθ : algebraMap E (w.adicCompletion E) θ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap E (w.adicCompletion E)).injective).mpr hq.root_ne_zero
  have hnu : ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) u) := by
    intro h
    apply hwu
    have h' := h.map φ
    rwa [hφ] at h'
  have hnuδ : ¬ IsSquare (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (u * δ)) := by
    intro h
    apply hwu
    have h' := h.map φ
    rw [hφ, map_mul, map_mul, ← hq.sq, map_pow] at h'
    obtain ⟨r, hr⟩ := h'
    refine ⟨r / algebraMap E (w.adicCompletion E) θ, ?_⟩
    rw [div_mul_div_comm, ← hr]
    field_simp
  have hval : ∀ x : F, Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
      (w.under (𝓞 F)).valuation F x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (w.under (𝓞 F)) x
  have h2 : Valued.v (2 : (w.under (𝓞 F)).adicCompletion F) = 1 := by
    rw [show (2 : (w.under (𝓞 F)).adicCompletion F) = algebraMap F _ 2 from (map_ofNat _ 2).symm,
      hval]
    simpa using hgood _ hvS (Units.mk0 (2 : F) two_ne_zero) (Finset.mem_insert_self _ _)
  have hvu : Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) u) = 1 := by
    rw [hval]
    simpa using hgood _ hvS (Units.mk0 u hu)
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hvuδ : Valued.v (algebraMap F ((w.under (𝓞 F)).adicCompletion F) (u * δ)) = 1 := by
    rw [hval]
    simpa using hgood _ hvS (Units.mk0 (u * δ) (mul_ne_zero hu hδ))
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  obtain ⟨s, hs⟩ := isSquare_mul_of_nonsquare_units F (w.under (𝓞 F)) h2 _ _ hvu hvuδ hnu hnuδ
  have ha : algebraMap F ((w.under (𝓞 F)).adicCompletion F) u ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F _).injective).mpr hu
  refine ⟨w.under (𝓞 F), fun h => hvS (hS₀ h), ⟨s / algebraMap F _ u, ?_⟩, hnu⟩
  rw [div_mul_div_comm, ← hs, map_mul]
  field_simp

end GlobalTheory.QNorm
