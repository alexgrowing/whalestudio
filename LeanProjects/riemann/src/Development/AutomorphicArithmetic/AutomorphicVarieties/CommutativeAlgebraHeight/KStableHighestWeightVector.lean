import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplUniq
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.TensorProduct.Quotient

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem dim_eq_of_flat {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  have hl : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
      (by rw [← hm]; exact Ideal.le_comap_map)⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [hm, Ideal.map_quotient_self] at h
  simp at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim, h]

private theorem dim_quot_eq_of_flat {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (J : Ideal A) :
    ringKrullDim (B ⧸ J.map (algebraMap A B)) = ringKrullDim (A ⧸ J) := by
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Ideal.map_top]
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  have hJm : J ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hJ
  have hIm : J.map (algebraMap A B) ≤ maximalIdeal B := hm ▸ Ideal.map_mono hJm
  have hI : J.map (algebraMap A B) ≠ ⊤ :=
    ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hIm
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : Nontrivial (B ⧸ J.map (algebraMap A B)) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (A ⧸ J) := .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (B ⧸ J.map (algebraMap A B)) :=
    .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : Module.Flat (A ⧸ J) (B ⧸ J.map (algebraMap A B)) := by
    have e : (B ⧸ J.map (algebraMap A B)) ≃ₗ[A] TensorProduct A (A ⧸ J) B :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toLinearEquiv.restrictScalars A).trans
        (TensorProduct.comm A B (A ⧸ J))
    haveI := Module.Flat.baseChange A (A ⧸ J) B
    exact Module.Flat.of_linearEquiv (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e)
  apply dim_eq_of_flat
  have hmA : maximalIdeal (A ⧸ J) = (maximalIdeal A).map (Ideal.Quotient.mk J) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJm))).symm
  have hmB : maximalIdeal (B ⧸ J.map (algebraMap A B)) =
      (maximalIdeal B).map (Ideal.Quotient.mk (J.map (algebraMap A B))) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIm))).symm
  rw [hmA, hmB, Ideal.map_map, ← hm, Ideal.map_map]
  congr 1

theorem UpperTheory.V.CA.c3c :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ I : Ideal C, ringKrullDim (R ⧸ I.map (algebraMap C R)) = dimAt x I) ∧ ∀ (I : Ideal C) (q : Ideal R), I ≤ q.comap (algebraMap C R) → ringKrullDim (R ⧸ q) ≤ dimAt x I := by
  intro C R _ _ _ _ _ x _ hR
  obtain ⟨_, ⟨e⟩, hmap⟩ := cpl_uniq x hR
  haveI := hR.noeth
  haveI : IsNoetherianRing (Cpl x) := isNoetherianRing_of_ringEquiv R e.toRingEquiv
  have hmapI : ∀ I : Ideal C,
      I.map (algebraMap C (Cpl x)) = (I.map (algebraMap C R)).map (e.toRingEquiv : R →+* Cpl x) := by
    intro I
    rw [Ideal.map_map]
    congr 1
    ext c
    simp
  have h1 : x.map (algebraMap C (Cpl x)) =
      (maximalIdeal (Localization.AtPrime x)).map (algebraMap (Localization.AtPrime x) (Cpl x)) := by
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.map_map,
      Localization.AtPrime.map_eq_maximalIdeal]
  have hm : (maximalIdeal (Localization.AtPrime x)).map
      (algebraMap (Localization.AtPrime x) (Cpl x)) = maximalIdeal (Cpl x) := by
    rw [← h1, hmapI, hmap]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.toRingEquiv)
  have key : ∀ I : Ideal C, ringKrullDim (R ⧸ I.map (algebraMap C R)) = dimAt x I := by
    intro I
    unfold dimAt
    rw [← dim_quot_eq_of_flat hm (I.map (algebraMap C (Localization.AtPrime x))), Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e.toRingEquiv (hmapI I))
  refine ⟨key, fun I q hq => ?_⟩
  rw [← key I]
  have hle : I.map (algebraMap C R) ≤ q := Ideal.map_le_iff_le_comap.mpr hq
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
