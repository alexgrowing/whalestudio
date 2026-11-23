import Development.EtaleCohomology.CohomologicalPurity.LeafHtpyPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.HtpyZeroPf

theorem eqv_of_iso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) : Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem off_bot_empty (B : Type) [CommRing B] (J : Ideal B) (hJ : J = ⊥) : IsEmpty (off B J) := by
  refine ⟨fun x => x.2 ?_⟩
  subst hJ
  change ((⊥ : Ideal B) : Set B) ⊆ ((x.1 : PrimeSpectrum B).asIdeal : Set B)
  intro a ha
  rw [SetLike.mem_coe, Ideal.mem_bot] at ha
  rw [SetLike.mem_coe, ha]
  exact Ideal.zero_mem _

theorem isIso_of_empty {X Y : Scheme.{0}} (f : X ⟶ Y) [IsEmpty X] [IsEmpty Y] : IsIso f :=
  ⟨⟨isInitialOfIsEmpty.to X, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩⟩

end HtpyZeroPf

theorem LeafHtpyZero_of : LeafHtpyZero := by
  intro _ q _ A _ h i
  have : IsEmpty (off A ⊥) := HtpyZeroPf.off_bot_empty A ⊥ rfl
  have : IsEmpty (off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C)) :=
    HtpyZeroPf.off_bot_empty _ _ (Ideal.map_bot)
  have : IsEmpty (off A ⊥).toScheme := inferInstanceAs (IsEmpty (off A ⊥))
  have : IsEmpty (off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C)).toScheme :=
    inferInstanceAs (IsEmpty (off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C)))
  have := HtpyZeroPf.isIso_of_empty
    ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)
  exact HtpyZeroPf.eqv_of_iso _ _

end LateralTheory.CohomologicalPurity.Thom
