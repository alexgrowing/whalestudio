import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem etale_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.Etale)
    (σ : Type) : (MvPolynomial.map (σ := σ) φ).Etale := by
  algebraize [φ]
  let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := A) (S := B)
  have h : Algebra.IsPushout A (MvPolynomial σ A) B (MvPolynomial σ B) := inferInstance
  haveI := h.symm
  exact RingHom.Etale.isStableUnderBaseChange A B (MvPolynomial σ A) (MvPolynomial σ B) hφ

private theorem etale_open {R : Type} [CommRing R] (U : (Spec (CommRingCat.of R)).Opens)
    (hU : IsAffineOpen U) :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of R))) ⊤ U le_top).hom.Etale := by
  have h0 : (Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of R))) ⊤ U le_top).hom.Etale :=
    HasRingHomProperty.appLE @Etale (𝟙 _) inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  exact RingHom.Etale.respectsIso.right _
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h0

private def subst (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    MvPolynomial (Fin (D + 1)) O →+* MvPolynomial (Fin D) O :=
  (MvPolynomial.aeval (Fin.cons (MvPolynomial.C ϖ) MvPolynomial.X :
    Fin (D + 1) → MvPolynomial (Fin D) O)).toRingHom

private theorem subst_C (O : Type) [CommRing O] (ϖ : O) (D : ℕ) (r : O) :
    subst O ϖ D (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [subst]

private theorem subst_X_zero (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    subst O ϖ D (MvPolynomial.X 0) = MvPolynomial.C ϖ := by
  simp [subst]

private theorem subst_X_succ (O : Type) [CommRing O] (ϖ : O) (D : ℕ) (i : Fin D) :
    subst O ϖ D (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [subst]

private theorem prod_first (O : Type) [CommRing O] (D : ℕ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1), MvPolynomial.X i) =
      (MvPolynomial.X 0 : MvPolynomial (Fin (D + 1)) O) := by
  have h : Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1) = {0} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩
      exact Fin.ext (by simp only [Fin.val_zero]; omega)
    · rintro rfl
      exact ⟨Finset.mem_univ _, by simp only [Fin.val_zero]; omega⟩
  rw [h, Finset.prod_singleton]

private def modelEquiv (O : Type) [CommRing O] (ϖ : O) (D : ℕ) :
    (MvPolynomial (Fin (D + 1)) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin (D + 1) => (i : ℕ) < 1),
      MvPolynomial.X i) - MvPolynomial.C ϖ}) ≃+* MvPolynomial (Fin D) O :=
  RingEquiv.ofRingHom
    (Ideal.Quotient.lift _ (subst O ϖ D) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [prod_first, map_mul, map_sub, subst_X_zero, subst_C, sub_self, mul_zero]))
    ((Ideal.Quotient.mk _).comp (MvPolynomial.rename Fin.succ).toRingHom)
    (by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [subst_C]
      · simp [subst_X_succ])
    (by
      refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
      · simp [subst_C]
      · refine Fin.cases ?_ (fun j => ?_) i
        · simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk, subst_X_zero, RingHom.id_apply]
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.rename_C]
          refine (Ideal.Quotient.eq.mpr ?_).symm
          rw [prod_first]
          exact Ideal.mem_span_singleton_self _
        · simp [subst_X_succ])

theorem smSst : SmSst := by
  intro O _ ϖ X p _ x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth p x
  obtain ⟨n, g, hgC, hg⟩ := hs.exists_etale_mvPolynomial
  have hf := etale_open (R := O) U hU
  refine ⟨V, hV, hx, n + 1, 1, le_rfl, by omega,
    (g.comp (MvPolynomial.map ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top).hom)).comp
        (modelEquiv O ϖ n).toRingHom, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (modelEquiv O ϖ n).bijective)
      (RingHom.Etale.stableUnderComposition _ _ (etale_map _ hf _) hg)
  · refine RingHom.ext fun r => ?_
    have e1 : Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top ≫
        Scheme.Hom.appLE p U V e = Scheme.Hom.appLE p ⊤ V le_top := by
      refine (Scheme.Hom.appLE_comp_appLE p (𝟙 _) ⊤ U V le_top e).trans ?_
      simp
    have e2 := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom r)) e1
    have e3 := RingHom.congr_fun hgC (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫
      Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of O))) ⊤ U le_top).hom r)
    have e4 : (modelEquiv O ϖ n) (algebraMap O _ r) = MvPolynomial.C r := subst_C O ϖ n r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e4, MvPolynomial.map_C]
    exact e3.trans e2

end UpperTheory.Gal.KunnethLefschetz.G
