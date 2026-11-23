import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PhiMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.StableField

open IsLocalRing UpperTheory.V.Fr

private theorem exists_field_embedding_of_domain (D : Type) [CommRing D] [IsDomain D] :
    ∃ (K : Type) (_ : Field K) (j : D →+* K), Function.Injective j := by
  set_option synthInstance.maxHeartbeats 400000 in
  exact ⟨FractionRing D, inferInstance, algebraMap D _, IsFractionRing.injective D (FractionRing D)⟩

private theorem exists_algClosed_embedding_of_field (F : Type) [Field F] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : F →+* K), Function.Injective j :=
  ⟨AlgebraicClosure F, inferInstance, inferInstance, algebraMap F _, RingHom.injective _⟩

private theorem exAlgCl0 (R : Type) [CommRing R] (P : Ideal R) [P.IsPrime] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : R →+* K), RingHom.ker j = P := by
  haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨K0, hK0, j0, hj0⟩ := exists_field_embedding_of_domain (R ⧸ P)
  obtain ⟨K, hK, hc, j, hj⟩ := exists_algClosed_embedding_of_field K0
  refine ⟨K, hK, hc, (j.comp j0).comp (Ideal.Quotient.mk P), ?_⟩
  have hinj : Function.Injective (j.comp j0) := fun a b h => hj0 (hj h)
  rw [RingHom.ker_comp_of_injective _ hinj, Ideal.mk_ker]

private theorem exAlgCl (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (P : Ideal R) [P.IsPrime] :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Algebra O K) (j : R →ₐ[O] K), RingHom.ker (j : R →+* K) = P := by
  obtain ⟨K, hK, hc, j, hj⟩ := exAlgCl0 R P
  letI : Algebra O K := (j.comp (algebraMap O R)).toAlgebra
  exact ⟨K, hK, hc, inferInstance, ⟨j, fun _ => rfl⟩, hj⟩

private theorem ringHom_injective_of_fields {F K : Type} [Field F] [Field K] (g : F →+* K) :
    Function.Injective g :=
  RingHom.injective _

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Pr.stableOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.StableOf := by
  intro l _ O _ _ _ _ _ F n T
  unfold UpperTheory.V.Pr.Setup.StableOf
  intro Φ hΦ x L P _ hTI
  have hn := T.n23
  have hok := T.ok
  obtain ⟨K, hK, hc, _, j, hj⟩ := exAlgCl O L.R P
  let f : T.S.A →ₐ[O] K := j.comp L.ι
  have hkerf : RingHom.ker (f : T.S.A →+* K) = L.im P := by
    show RingHom.ker ((j : L.R →+* K).comp (L.ι : T.S.A →+* L.R)) =
      Ideal.comap (L.ι : T.S.A →+* L.R) P
    rw [← RingHom.comap_ker, hj]
  have hloc := (loc_rho hok hn T.S x L).2.2.1 P
  have hTIS : T.S.u.TI (RingHom.ker (f : T.S.A →+* K)) := by
    rw [hkerf]
    unfold NRep.TI NRep.OffTri at hTI ⊢
    exact ⟨⟨fun h => hTI.1.1 (hloc.1.mpr h), fun h => hTI.1.2 (hloc.2.1.mpr h)⟩,
      fun h3 h => hTI.2 h3 (hloc.2.2.mpr h)⟩
  have hirr := ((types hok hn T.S K (f : T.S.A →+* K)).1).mpr hTIS
  have hirr2 := T.K.tw_irr (NRep.map (f : T.S.A →+* K) T.S.u) hirr
  have hΦ' : T.K.IsPhi T.B T.S Φ := hΦ
  have hm := UpperTheory.V.Pr.TwLink.IsPhi.maps T.K hΦ' f
  unfold UpperTheory.V.W.Pair.Maps at hm
  have hL : RingHom.ker ((f.comp (T.S.inc.comp Φ)) : T.B.B →+* K) =
      Ideal.comap ((T.phi Φ L) : T.B.B →+* L.R) P := by
    show RingHom.ker ((j : L.R →+* K).comp ((T.phi Φ L) : T.B.B →+* L.R)) = _
    rw [← RingHom.comap_ker, hj]
  have hR : RingHom.ker (T.B.toKap (T.back Φ L P)) = (T.back Φ L P).asIdeal := by
    unfold UpperTheory.V.W.UniversalOrdinaryDeterminantRing.toKap
    refine (RingHom.ker_comp_of_injective _ (ringHom_injective_of_fields _)).trans ?_
    exact Ideal.ker_algebraMap_residueField _
  unfold UpperTheory.V.W.UniversalOrdinaryDeterminantRing.IsStable
  refine UpperTheory.V.CA.stable_field T.B.u.D ((f.comp (T.S.inc.comp Φ)) : T.B.B →+* K)
    (T.B.toKap (T.back Φ L P)) ?_ ⟨_, hirr2, hm.1⟩
  rw [hL, hR]
  rfl
