import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MaxPt

theorem eq_top_of_forall_cxPts_mem : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens),
    (∀ z : CxPts p (RingHom.id ℂ), z ∈ CxPts.ptsIn p (RingHom.id ℂ) U) → U = ⊤ := by
  intro X p _ U hall
  by_contra hU
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ U := by
    by_contra h
    push_neg at h
    exact hU (eq_top_iff.2 fun y _ => h y)
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hV : IsAffineOpen V := hV
  let S : Set (PrimeSpectrum Γ(X, V)) := {η | hV.fromSpec η ∉ U}
  have hS : IsClosed S := by
    have : IsOpen {η : PrimeSpectrum Γ(X, V) | hV.fromSpec η ∈ U} :=
      U.isOpen.preimage hV.fromSpec.continuous
    exact this.isClosed_compl
  have hSne : S.Nonempty := by
    have : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
    obtain ⟨ξ, hξ⟩ := this
    exact ⟨ξ, by show hV.fromSpec ξ ∉ U; rw [hξ]; exact hx⟩
  obtain ⟨η, hηS, hηc⟩ := hS.exists_closed_singleton hSne
  have hm : η.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal η).1 hηc
  set m := η.asIdeal
  have h1 := LocallyOfFiniteType.finiteType_of_affine_subset p (isAffineOpen_top (Sp ℂ)) hV (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p V).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, V) := (algX p V).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, V) := hft
  letI : Field (Γ(X, V) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(X, V) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, V) ⧸ m)
  have hbij : Function.Bijective (algebraMap ℂ (Γ(X, V) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃+* (Γ(X, V) ⧸ m) := RingEquiv.ofBijective _ hbij
  let φ : Γ(X, V) →+* ℂ := (e.symm : (Γ(X, V) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)
  have hφ : ∀ a, φ (algX p V a) = (RingHom.id ℂ) a := by
    intro a
    show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, V) a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  have hker : RingHom.ker φ = m := by
    ext f
    rw [RingHom.mem_ker]
    show e.symm (Ideal.Quotient.mk m f) = 0 ↔ f ∈ m
    rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  have hz := CxPts.mem_ptsIn.1 (hall (CxPts.ofHom hV φ hφ))
  have hpt : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ) = η := by
    apply PrimeSpectrum.ext
    show Ideal.comap φ (IsLocalRing.maximalIdeal ℂ) = m
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, hker]
  have : (CxPts.ofHom hV φ hφ).1 (IsLocalRing.closedPoint ℂ) = hV.fromSpec η := by
    show (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) (IsLocalRing.closedPoint ℂ) = _
    show hV.fromSpec (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint ℂ)) = _
    rw [hpt]
  exact hηS (this ▸ hz)

end GlobalTheory.MaxPt
