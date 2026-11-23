import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.CompleteFin

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem isMax_of_le {R : Type*} [CommRing R] (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    (P : Ideal R) [hP : P.IsPrime] (h : I ≤ P) : P.IsMaximal := by
  have h1 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have h2 : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have h3 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (K := P.map (Ideal.Quotient.mk I))
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.2 h] at h3

private theorem art_pow {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] (k : ℕ) : IsArtinianRing (R ⧸ I ^ k) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h0 : I ^ k ≤ p.comap (Ideal.Quotient.mk (I ^ k)) := by
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h1 : (p.comap (Ideal.Quotient.mk (I ^ k))).IsMaximal :=
    isMax_of_le I _ (Ideal.IsPrime.le_of_pow_le h0)
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (I ^ k)) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (I ^ k))
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.tateH1FinitenessAtPlacesOver :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [IsArtinianRing (R ⧸ I)] [Module.Finite R M], OrdAdm M I := by
  intro R _ M _ _ _ I _ _ _
  refine ⟨UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin I, fun k => ?_⟩
  haveI := art_pow I k
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  haveI : Module.Finite (R ⧸ I ^ k) (M ⧸ (I ^ k • ⊤ : Submodule R M)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact isArtinian_of_surjective_algebraMap (R := R ⧸ I ^ k) Ideal.Quotient.mk_surjective
