import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomainStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableSpecialFibrePropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableGenericFibreLocalizationStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison

section Ring

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
  (m r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ m)

include hϖ h1 h2 in
theorem ssModel_isDomain : IsDomain (GlobalTheory.Et.ssModel O ϖ m r) := GlobalTheory.T.semistable_model_ring_isDomain O ϖ hϖ m r h1 h2

include hϖ h1 h2 in
theorem ssModel_algebraMap_ne_zero : algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ ≠ 0 := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  intro h
  have h0 : ϖ ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have := GlobalTheory.LogCris.model_mul_eq_zero ϖ h0 (1 : GlobalTheory.Et.ssModel O ϖ m r) (by rw [h, zero_mul])
  exact one_ne_zero this

include hϖ h1 h2 in
theorem ssModel_algebraMap_injective : Function.Injective (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra hc0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  rw [map_mul, map_pow] at hc
  rcases mul_eq_zero.1 hc with h | h
  · exact (u.isUnit.map (algebraMap O _)).ne_zero h
  · exact ssModel_algebraMap_ne_zero O ϖ hϖ m r h1 h2 (pow_eq_zero_iff'.1 h).1

include hϖ h1 h2 in
theorem ssModel_normal (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F] :
    IsDomain (GlobalTheory.Et.ssModel O ϖ m r) ∧ IsIntegrallyClosed (GlobalTheory.Et.ssModel O ϖ m r) := by
  have hd := ssModel_isDomain O ϖ hϖ m r h1 h2
  refine ⟨hd, ?_⟩
  have ht := ssModel_algebraMap_ne_zero O ϖ hϖ m r h1 h2
  have hred := GlobalTheory.T.semistable_special_fibre_property O ϖ hϖ m r h1 h2
  have hs := GlobalTheory.T.semistable_generic_fibre_localization O ϖ hϖ m r h1 h2 F
  haveI : Smooth (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) ϖ))) :=
    HasRingHomProperty.Spec_iff.mpr hs
  have hn := GlobalTheory.isNormalScheme_of_smooth (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) ϖ)))
  haveI : IsDomain (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hic := (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain
    (CommRingCat.of (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)))).mp hn
  exact GlobalTheory.T.isIntegrallyClosed_of_reduced_quotient_localization _ _ ht hred hic

include hϖ h1 h2 in
theorem ssModel_flat : Module.Flat O (GlobalTheory.Et.ssModel O ϖ m r) := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  have hi := ssModel_algebraMap_injective O ϖ hϖ m r h1 h2
  haveI : Module.IsTorsionFree O (GlobalTheory.Et.ssModel O ϖ m r) := Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  infer_instance

end Ring

section Scheme

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] K]

theorem good_isNormalScheme (M : Model l K) (hM : M.Good) : GlobalTheory.IsNormalScheme M.X := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  haveI := OK_away hϖ
  refine GlobalTheory.IsNormalScheme.of_forall_exists_opens fun x => ?_
  obtain ⟨U, hU, hx, m, r, h1, h2, ψ, hψ, -⟩ := hss x
  refine ⟨U, hx, ?_⟩
  rw [GlobalTheory.IsNormalScheme.iff_spec_of_isAffineOpen hU]
  obtain ⟨hd, hic⟩ := ssModel_normal (OK l K) ϖ hϖ m r h1 h2 K
  haveI : Etale (Spec.map (CommRingCat.ofHom ψ)) := HasRingHomProperty.Spec_iff.mpr hψ
  exact GlobalTheory.isNormalScheme_of_smooth (Spec.map (CommRingCat.ofHom ψ))

theorem good_isLocallyNoetherian (M : Model l K) (hM : M.Good) : IsLocallyNoetherian M.X := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  choose U hU hx m r h1 h2 ψ hψ _hc using hss
  refine isLocallyNoetherian_of_affine_cover (S := fun x => ⟨U x, hU x⟩) ?_ fun x => ?_
  · refine top_le_iff.mp fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx y⟩
  · letI := (ψ x).toAlgebra
    haveI : Algebra.Etale _ _ := hψ x
    exact Algebra.FiniteType.isNoetherianRing (GlobalTheory.Et.ssModel (OK l K) ϖ (m x) (r x)) Γ(M.X, U x)

theorem good_flat (M : Model l K) (hM : M.Good) : Flat M.p := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  choose U hU hx m r h1 h2 ψ hψ hc using hss
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (U := fun x => ⟨U x, hU x⟩) ?_ fun x => ?_
  · refine top_le_iff.mp fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx y⟩
  · have e : (M.p.appLE ⊤ (U x) le_top) = (Scheme.ΓSpecIso (CommRingCat.of (OK l K))).hom ≫
        CommRingCat.ofHom ((ψ x).comp (algebraMap (OK l K) _)) := by
      rw [hc x]; simp
    show RingHom.Flat (M.p.appLE ⊤ (U x) le_top).hom
    rw [e, CommRingCat.hom_comp]
    refine RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) ?_
    haveI : Etale (Spec.map (CommRingCat.ofHom (ψ x))) := HasRingHomProperty.Spec_iff.mpr (hψ x)
    have hf : RingHom.Flat (ψ x) := HasRingHomProperty.Spec_iff.mp (inferInstance : Flat (Spec.map (CommRingCat.ofHom (ψ x))))
    refine RingHom.Flat.comp ?_ hf
    exact RingHom.flat_algebraMap_iff.mpr (ssModel_flat (OK l K) ϖ hϖ (m x) (r x) (h1 x) (h2 x))

end Scheme

end CrystallineSemistableComparison
