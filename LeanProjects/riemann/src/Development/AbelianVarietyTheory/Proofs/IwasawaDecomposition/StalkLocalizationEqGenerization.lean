import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem stalk_localization_atPrime_eq_stalk_generization :
    ∀ (X : Scheme.{0}) (x : X) (q : Ideal (X.presheaf.stalk x)) [q.IsPrime],
      ∃ (y : X) (h : y ⤳ x) (e : Localization.AtPrime q ≃+* X.presheaf.stalk y),
        ∀ s, e (algebraMap _ _ s) = (X.presheaf.stalkSpecializes h).hom s := by
  intro X x q _
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  let xU : U := ⟨x, hxU⟩
  let algX : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf xU
  have hlocX : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf xU).asIdeal :=
    hU.isLocalization_stalk xU
  set Px := hU.primeIdealOf xU with hPx
  let P' : PrimeSpectrum Γ(X, U) :=
    ⟨q.comap (algebraMap Γ(X, U) (X.presheaf.stalk x)), inferInstance⟩
  have hP'x : P' ≤ Px := by
    intro a ha
    by_contra hna
    have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) a) :=
      IsLocalization.map_units (X.presheaf.stalk x) (⟨a, hna⟩ : Px.asIdeal.primeCompl)
    exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem q ha hu)
  set y := hU.fromSpec P' with hy
  have hyU : y ∈ U := by
    have : y ∈ (U : Set X) := by rw [← hU.range_fromSpec]; exact ⟨P', rfl⟩
    exact this
  have hsp : y ⤳ x := by
    have h1 : P' ⤳ Px := (PrimeSpectrum.le_iff_specializes P' Px).mp hP'x
    have h2 := h1.map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf xU] at h2
  let yU : U := ⟨y, hyU⟩
  let algY : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have hlocY : IsLocalization.AtPrime (X.presheaf.stalk y) P'.asIdeal :=
    hU.isLocalization_stalk' P' hyU
  let T := Localization.AtPrime q
  have hT : IsLocalization.AtPrime T P'.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Px.asIdeal.primeCompl) (S := X.presheaf.stalk x) (T := T) q
  let φ : X.presheaf.stalk y ≃ₐ[Γ(X, U)] T := IsLocalization.algEquiv P'.asIdeal.primeCompl _ _
  refine ⟨y, hsp, φ.symm.toRingEquiv, ?_⟩
  intro s
  have key : (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (X.presheaf.stalk x) T)) =
      (X.presheaf.stalkSpecializes hsp).hom := by
    apply IsLocalization.ringHom_ext Px.asIdeal.primeCompl
    ext a
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk x) T]
    have h1 : φ.symm.toRingEquiv.toRingHom (algebraMap Γ(X, U) T a) =
        algebraMap Γ(X, U) (X.presheaf.stalk y) a :=
      φ.symm.commutes a
    rw [h1]
    show X.presheaf.germ U y hyU a =
      (X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ U x hxU a)
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU hsp a).symm
  exact congrArg (fun f => f s) key

end GlobalTheory
