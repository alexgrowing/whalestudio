import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassFieldArtin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField IsDedekindDomain Module IntermediateField WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K]

omit [NumberField K] in

theorem mem_fixingSubgroup_adjoin_simple_iff {F E : Type*} [Field F] [Field E] [Algebra F E]
    (α : E) (τ : E ≃ₐ[F] E) : τ ∈ (F⟮α⟯).fixingSubgroup ↔ τ α = α := by
  constructor
  · intro hτ
    exact (mem_fixingSubgroup_iff _ _).1 hτ α (mem_adjoin_simple_self F α)
  · intro hτ
    have hst : τ ∈ MulAction.stabilizer (E ≃ₐ[F] E) α := hτ
    have hle : F⟮α⟯ ≤ fixedField (Subgroup.zpowers τ) := by
      rw [adjoin_simple_le_iff, mem_fixedField_iff]
      intro f hf
      exact (Subgroup.zpowers_le.2 hst) hf
    exact (le_iff_le _ _).1 hle (Subgroup.mem_zpowers τ)

include hK in

theorem adjoin_j_eq_hilbertClassField (x : ELL K) : K⟮ELL.j x⟯ = hilbertClassField K ℂ := by
  classical
  obtain ⟨L, hHL, hLfin, hLgal, hL, E, hEl, hE, hiso⟩ :=
    exists_models_isogenous hK (hilbertClassField K ℂ)
  have key := galClassOf_eq_artin hK L hHL hL E hE hiso
  set a : L := ⟨ELL.j x, hL x⟩
  have hfix : ∀ τ : L ≃ₐ[K] L, τ ∈ (K⟮a⟯).fixingSubgroup ↔ τ ∈ (restrict hHL).fixingSubgroup := by
    intro τ
    rw [mem_fixingSubgroup_restrict_iff, ← (hilbertClassFieldArtinEquiv K ℂ).symm.map_eq_one_iff,
      ← key, mem_fixingSubgroup_adjoin_simple_iff]
    constructor
    · intro h1
      have h2 := galClassOf_apply_j hK L hL τ x
      rw [h1] at h2
      exact (ell_smul_eq_self_iff (algebraMap K ℂ) hK _ x).1 (ELL.j_injective h2.symm)
    · intro h1
      apply Subtype.ext
      rw [galClassOf_apply_j hK L hL τ x, h1, ellMulAction_one_smul]
  have hJH : K⟮a⟯ = restrict hHL :=
    calc K⟮a⟯ = fixedField (fixingSubgroup K⟮a⟯) := (IsGalois.fixedField_fixingSubgroup _).symm
      _ = fixedField (fixingSubgroup (restrict hHL)) := by
        congr 1
        ext τ
        exact hfix τ
      _ = restrict hHL := IsGalois.fixedField_fixingSubgroup _
  have h := congrArg lift hJH
  rwa [lift_adjoin_simple, lift_restrict] at h

include hK in

theorem adjoin_j_curve_eq_hilbertClassField (E : CMCurve K) :
    K⟮E.curve.j⟯ = hilbertClassField K ℂ := by
  rw [← ELL.j_toEll]
  exact adjoin_j_eq_hilbertClassField hK E.toEll

include hK in

theorem j_mem_hilbertClassField (x : ELL K) : ELL.j x ∈ hilbertClassField K ℂ := by
  rw [← adjoin_j_eq_hilbertClassField hK x]
  exact mem_adjoin_simple_self K _

theorem hilbertClassFieldArtinEquiv_apply_j (a : ClassGroup (𝓞 K)) (y : ELL K) :
    ((hilbertClassFieldArtinEquiv K ℂ a ⟨ELL.j y, j_mem_hilbertClassField hK y⟩ :
        hilbertClassField K ℂ) : ℂ) =
      ELL.j ((ellMulAction (algebraMap K ℂ) hK).smul a y) := by
  classical
  obtain ⟨L, hHL, hLfin, hLgal, hL, E, hEl, hE, hiso⟩ :=
    exists_models_isogenous hK (hilbertClassField K ℂ)
  obtain ⟨τ, hτ⟩ := galRestrict_surjective hHL (hilbertClassFieldArtinEquiv K ℂ a)
  have hcls : galClassOf hK L hL τ = a := by
    rw [galClassOf_eq_artin hK L hHL hL E hE hiso, hτ, MulEquiv.symm_apply_apply]
  rw [← hτ, galRestrict_apply, ← hcls, ← galClassOf_apply_j hK L hL τ y]
  rfl

include hK in

theorem j_weierstrassCurve_mem_hilbertClassField (Λ : PeriodPair)
    (hΛ : latticeEnd Λ = cmRing (algebraMap K ℂ)) :
    (weierstrassCurve Λ).j ∈ hilbertClassField K ℂ :=
  j_mem_hilbertClassField hK (ellOf (algebraMap K ℂ) Λ hΛ)

theorem hilbertClassFieldArtinEquiv_apply_j_weierstrassCurve (Λ Λ' : PeriodPair)
    (hΛ : latticeEnd Λ = cmRing (algebraMap K ℂ)) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : Λ'.lattice = idealLattice (algebraMap K ℂ) ↑𝔞⁻¹ * Λ.lattice) :
    ((hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk K 𝔞)
        ⟨(weierstrassCurve Λ).j, j_weierstrassCurve_mem_hilbertClassField hK Λ hΛ⟩ :
        hilbertClassField K ℂ) : ℂ) = (weierstrassCurve Λ').j := by
  obtain ⟨L'', hL''lat, hL''⟩ := exists_lattice_mul (algebraMap K ℂ) hK Λ hΛ 𝔞
  have hΛ' : latticeEnd Λ' = cmRing (algebraMap K ℂ) := by
    rw [← hL'']
    ext α
    show (∀ l ∈ Λ'.lattice, α * l ∈ Λ'.lattice) ↔ ∀ l ∈ L''.lattice, α * l ∈ L''.lattice
    rw [h, hL''lat]
  have e := hilbertClassFieldArtinEquiv_apply_j hK (ClassGroup.mk K 𝔞) (ellOf (algebraMap K ℂ) Λ hΛ)
  rw [classGroup_smul_ellOf (algebraMap K ℂ) hK Λ Λ' hΛ hΛ' 𝔞 h] at e
  exact e

end

end Elliptic
end GroundTheory.Global
