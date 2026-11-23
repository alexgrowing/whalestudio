import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

theorem exists_fibre_generic_of_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (π : R), Prime π → ∃ ξ : X, (q ξ).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧ Irreducible (X.presheaf.germ ⊤ ξ trivial (constFn q ⊤ π)) := by
  intro R _ _ _ _ X _ q _ _ π hπp
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπp.ne_zero).2 hπp
  let v : Sp R := ⟨Ideal.span {π}, hP⟩
  let V := Localization.AtPrime v.asIdeal
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span {algebraMap R V π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hne : algebraMap R V π ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective V v.asIdeal.primeCompl_le_nonZeroDivisors)).2 hπp.ne_zero
  have : IsNoetherianRing V := IsLocalization.isNoetherianRing v.asIdeal.primeCompl V inferInstance
  have hnf : ¬ IsField V := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hne
  have hpr : Submodule.IsPrincipal (IsLocalRing.maximalIdeal V) := ⟨⟨_, hmax⟩⟩
  have : IsDiscreteValuationRing V :=
    ((IsDiscreteValuationRing.TFAE V hnf).out 0 4).mpr hpr
  have hπ : Irreducible (algebraMap R V π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  let l := spMap (algebraMap R V)
  have : Flat l := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : IsPreimmersion l := IsPreimmersion.of_isLocalization v.asIdeal.primeCompl
  have H := IsPullback.of_hasPullback q l
  set ψ := pullback.fst q l
  set f := pullback.snd q l
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks ψ
  obtain ⟨h₁, h₂⟩ := DvrModel.isDiscreteValuationRing_stalk_generic hπ hs
  have h₃ := DvrModel.notMem_basicOpen_iff_specializes hπ hs
  have hlv : l (IsLocalRing.closedPoint V) = v :=
    PrimeSpectrum.ext (Localization.AtPrime.comap_maximalIdeal (I := v.asIdeal))
  have h₄ := (DvrModel.notMem_basicOpen_iff f hπ _).1 ((h₃ _).2 specializes_rfl)
  generalize (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) (genericPoint _) = ξ
    at h₁ h₂ h₃ h₄
  let E := (asIso (ψ.stalkMap ξ)).commRingCatIsoToRingEquiv
  refine ⟨ψ ξ, ?_, fun x hx => ?_,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, h₄, hlv]
  · obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback H x (IsLocalRing.closedPoint V)
      ((PrimeSpectrum.ext hx).trans hlv.symm)
    exact ((h₃ y).1 ((DvrModel.notMem_basicOpen_iff f hπ y).2 hy)).map ψ.continuous
  · rw [← MulEquiv.irreducible_iff E.toMulEquiv]
    convert h₂ using 1
    exact (ψ.germ_stalkMap_apply ⊤ ξ trivial _).trans
      (congrArg _ ((app_constFn H.w π).trans (constFn_top _ _)))

end GlobalTheory.VerticalUnit
