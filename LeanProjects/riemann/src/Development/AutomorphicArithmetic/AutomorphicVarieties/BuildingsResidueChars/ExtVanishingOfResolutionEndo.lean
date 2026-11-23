import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory Limits in
private theorem homologyMap_zero_of_f {C : Type*} [Category C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (Ψ : K ⟶ L) (q : ι) (h : Ψ.f q = 0) :
    HomologicalComplex.homologyMap Ψ q = 0 := by
  have h1 : HomologicalComplex.cyclesMap Ψ q = 0 := by
    rw [← cancel_mono (L.iCycles q), zero_comp, HomologicalComplex.cyclesMap_i, h, comp_zero]
  rw [← cancel_epi (K.homologyπ q), comp_zero, HomologicalComplex.homologyπ_naturality, h1, zero_comp]

open CategoryTheory Limits in
private theorem isZero_yoneda {R : Type*} [Ring R] {C : Type*} [Category C] [Abelian C]
    [Linear R C] {X : C} (Y : C) (P : ProjectiveResolution X) (e : P.complex ⟶ P.complex)
    (he : e ≫ P.π = P.π) (q : ℕ) (hq : e.f q = 0) :
    IsZero ((P.complex.linearYonedaObj R Y).homology q) := by
  let F := ((linearYoneda R C).obj Y).rightOp
  have h1 : Homotopy e (𝟙 P.complex) :=
    ProjectiveResolution.liftHomotopy (𝟙 X) e (𝟙 _) (by simpa using he) (by simp)
  have h2 := (F.mapHomotopy h1).unop
  have h3 := h2.homologyMap_eq q
  have hz : ((HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map e).op).f q = 0 := by
    show (F.map (e.f q)).unop = 0
    rw [hq, F.map_zero]
    rfl
  rw [homologyMap_zero_of_f _ q hz] at h3
  simp only [CategoryTheory.Functor.map_id, op_id, HomologicalComplex.homologyMap_id] at h3
  rw [IsZero.iff_id_eq_zero]
  exact h3.symm

open CategoryTheory Limits in
theorem UpperTheory.ext_vanishing_of_resolution_endo :
    UpperTheory.V.Af.BA.VanishOf := by
  intro Γ _ P e he q hq A
  have h2 : IsZero (groupCohomology A q) :=
    (isZero_yoneda (R := ℂ) A P e he q hq).of_iso (groupCohomologyIso A q P)
  haveI := ModuleCat.subsingleton_of_isZero h2
  exact rank_subsingleton' ℂ _
