import Development.EtaleCohomology.EtaleSheaves.LZProperCut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LZHensFinitePf

def HensIdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
  (e : B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)), IsIdempotentElem e →
  ∃ f : B, IsIdempotentElem f ∧ Ideal.Quotient.mk _ f = e

theorem hensIdemLift : HensIdemLift := by
  intro A _ _ _ B _ _ _ e he
  exact GlobalTheory.exists_idempotent_lift_of_henselian A (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective he

theorem idem_triv_of_preconnected (R : Type) [CommRing R] [PreconnectedSpace (PrimeSpectrum R)]
    (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · left
    apply he.eq_zero_of_isNilpotent
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    exact SetLike.coe_injective h
  · right
    have hz : PrimeSpectrum.zeroLocus ({e} : Set R) = ∅ := by
      rw [← compl_compl (PrimeSpectrum.zeroLocus ({e} : Set R)), ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, h,
        Set.compl_univ]
    have h1 : IsNilpotent (1 - e) := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply SetLike.coe_injective
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub, sub_sub_cancel, hz]
      rfl
    exact (sub_eq_zero.mp (he.one_sub.eq_zero_of_isNilpotent h1)).symm

theorem subsingleton_of_idem (R : Type) [CommRing R] [IsArtinianRing R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : Subsingleton (PrimeSpectrum R) := by
  have hp : PreconnectedSpace (PrimeSpectrum R) := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases h e he with rfl | rfl
    · left; simp
    · right; simp
  exact ⟨fun x y => hp.constant (f := id) continuous_id⟩

theorem LZHensFinite_of_lift (hL : HensIdemLift) : LateralTheory.E.LZProperCut.LZHensFinite := by
  intro A _ _ _ B _ _ _ hB
  have : ConnectedSpace (PrimeSpectrum B) := hB
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  set I := (IsLocalRing.maximalIdeal A).map (algebraMap A B) with hI
  have hle : ∀ M : Ideal B, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    have : (M.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  have htriv : ∀ e : B ⧸ I, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := hL A B e he
    rcases idem_triv_of_preconnected B f hf with rfl | rfl
    · left; simp
    · right; simp
  have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  let _ : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsArtinianRing (B ⧸ I) := IsArtinianRing.of_finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I)
  have hsub := subsingleton_of_idem (B ⧸ I) htriv
  have key : ∀ P : Ideal B, P.IsMaximal →
      P = (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) ∧ (P.map (Ideal.Quotient.mk I)).IsPrime := by
    intro P hP
    refine ⟨(Ideal.comap_map_mk (hle P hP)).symm, ?_⟩
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle P hP)
  apply IsLocalRing.of_unique_max_ideal
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  refine ⟨M, hM, fun N hN => ?_⟩
  obtain ⟨hN1, hN2⟩ := key N hN
  obtain ⟨hM1, hM2⟩ := key M hM
  have : (⟨_, hN2⟩ : PrimeSpectrum (B ⧸ I)) = ⟨_, hM2⟩ := Subsingleton.elim _ _
  exact hN1.trans ((congrArg (fun P : PrimeSpectrum (B ⧸ I) => P.asIdeal.comap (Ideal.Quotient.mk I)) this).trans hM1.symm)

end LateralTheory.E.LZHensFinitePf
