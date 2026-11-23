import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing

universe u

theorem IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsPrincipalIdealRing R := by
  have : IsDomain R := IsRegularLocalRing.isDomain
  have hreg := (isRegularLocalRing_iff R).mp inferInstance
  have hle : (maximalIdeal R).spanFinrank ≤ 1 := by
    rw [← hreg] at h; exact_mod_cast h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · have hbot : maximalIdeal R = ⊥ := (Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal R).fg_of_isNoetherianRing).mp h0
    let := ((isField_iff_maximalIdeal_eq).mpr hbot).toField
    infer_instance
  · have : IsDiscreteValuationRing R := IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp (by
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; exact h1)
    infer_instance

theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one {R : Type*}
    [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : UniqueFactorizationMonoid R :=
  have : IsDomain R := IsRegularLocalRing.isDomain
  have := IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one h
  inferInstance

theorem IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one {R : Type*}
    [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsIntegrallyClosed R :=
  have : IsDomain R := IsRegularLocalRing.isDomain
  have := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one h
  inferInstance

theorem ringKrullDim_localization_le_of_etale {P B : Type*} [CommRing P] [CommRing B]
    [Algebra P B] [Algebra.Etale P B] [IsRegularRing P] (Q : Ideal B) [Q.IsPrime] :
    ringKrullDim (Localization.AtPrime Q) ≤ ringKrullDim (Localization.AtPrime (Q.under P)) := by
  let p := Q.under P
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing P B
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hun : Algebra.IsUnramifiedAt P Q := inferInstance
  have hmap := ((Algebra.isUnramifiedAt_iff_map_eq P p Q).mp hun).2
  have h : (maximalIdeal (Localization.AtPrime p)).map
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact hmap
  calc ringKrullDim (Localization.AtPrime Q)
      ≤ (maximalIdeal (Localization.AtPrime Q)).spanFinrank :=
        ringKrullDim_le_spanFinrank_maximalIdeal _
    _ ≤ (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
        rw [← h]
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _
          (maximalIdeal (Localization.AtPrime p)).fg_of_isNoetherianRing
    _ = ringKrullDim (Localization.AtPrime p) :=
        (isRegularLocalRing_iff (Localization.AtPrime p)).mp inferInstance

open AlgebraicGeometry CategoryTheory

theorem ringKrullDim_stalk_le_of_smoothOfRelativeDimension {X : Scheme.{u}} {k : Type u} [Field k]
    (n : ℕ) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ n := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hUtop : U = ⊤ := eq_top_iff.mpr fun y _ ↦ Subsingleton.elim (f.base x) y ▸ e hx
  subst hUtop
  let eΓ := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
  have : IsRegularRing Γ(Spec (.of k), ⊤) := IsRegularRing.of_ringEquiv eΓ.symm
  have : IsNoetherianRing Γ(Spec (.of k), ⊤) := isNoetherianRing_of_ringEquiv k eΓ.symm
  have hdim0 : ringKrullDim Γ(Spec (.of k), ⊤) = 0 := by
    rw [ringKrullDim_eq_of_ringEquiv eΓ, ringKrullDim_eq_zero_of_field]
  algebraize [(f.appLE ⊤ V e).hom]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n
    Γ(Spec (.of k), ⊤) Γ(X, V)
  algebraize [g.toRingHom]
  set P := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := hV.isLocalization_stalk ⟨x, hx⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv (R := Γ(X, V)) P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv]
  refine (ringKrullDim_localization_le_of_etale (P := MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))
    P).trans ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (P.under (MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))) (Localization.AtPrime _)]
  refine (Ideal.height_le_ringKrullDim_of_isPrime).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hdim0]
  simp

end GroundTheory.Arith.SchemeCoh
