import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowLeIndexLocalNormsSqrtExtensionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTopStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissibleSupersetFinitePlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem normSub_eq_top_of_isSquare_image {F L : Type} [Field F] [Field L] [CharZero L]
    (φ : F →+* L) (δ : F) (hδ : δ ≠ 0) (h : IsSquare (φ δ)) (x : Fˣ) : x ∈ normSub φ δ := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hδ ((map_eq_zero φ).1 (by simpa using hr))
  refine ⟨(φ x + 1) / 2, (φ x - 1) / (2 * r), ?_⟩
  rw [hr]
  field_simp
  ring

theorem exists_not_mem_not_isSquare_completion :
    ∀ (F : Type) [Field F] [NumberField F] (u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), u ≠ 0 → ¬ IsSquare u → ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) u) := by
  classical
  intro F _ _ u S₀ hu hns
  by_contra hcon
  push Not at hcon
  have hle : ∀ S, locNorm F u S₀ ≤ locNorm F u S := by
    intro S x hx
    rw [locNorm, Subgroup.mem_inf] at hx ⊢
    refine ⟨?_, hx.2⟩
    have h1 := hx.1
    simp only [Subgroup.mem_iInf] at h1 ⊢
    intro v _
    by_cases hv : v ∈ S₀
    · exact h1 v hv
    · haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      exact normSub_eq_top_of_isSquare_image _ u hu (hcon v hv) x
  have hidx := (GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension F u S₀ hu).1
  haveI : (locNorm F u S₀).FiniteIndex := ⟨hidx⟩
  haveI : Fintype (Fˣ ⧸ locNorm F u S₀) := Fintype.ofFinite _
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F
    (insert (Units.mk0 u hu)
      (Finset.univ.image (fun q : Fˣ ⧸ locNorm F u S₀ => q.out))) S₀
  obtain ⟨S, hS, hadm⟩ := exists_admissible_superset_finite_places F S₁
  have hX := hS₁ S hS
  refine GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top F (Units.mk0 u hu) S hadm (hX _ (Finset.mem_insert_self _ _)) hns ?_
  rw [eq_top_iff]
  intro x _
  have hy : (QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out ∈ sUnits F S :=
    hX _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz : ((QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out)⁻¹ * x ∈ locNorm F u S₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have hx : x = (QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out *
      (((QuotientGroup.mk x : Fˣ ⧸ locNorm F u S₀).out)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hy (hle S hz)

end GlobalTheory.QNorm
