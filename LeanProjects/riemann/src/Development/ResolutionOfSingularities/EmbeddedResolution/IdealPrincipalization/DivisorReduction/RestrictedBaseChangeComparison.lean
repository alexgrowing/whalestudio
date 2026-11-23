import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.InducedSubschemePullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.FieldExtensionBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentsFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem smooth_of_isIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g] :
    AlgebraicGeometry.Smooth g := inferInstance

private theorem surjective_of_isIso {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g] :
    AlgebraicGeometry.Surjective g := inferInstance

private theorem comap_congr {X W : Scheme.{u}} {a b : W ⟶ X} (h : a = b)
    (I : X.IdealSheafData) : I.comap a = I.comap b := by
  subst h
  rfl

private theorem map_comap_map_comap_eq_map_comap_comp {X Y W : Scheme.{u}} (a : W ⟶ Y) (b : Y ⟶ X)
    (M : List X.IdealSheafData) :
    List.map (fun D : Y.IdealSheafData => D.comap a)
        (List.map (fun D : X.IdealSheafData => D.comap b) M)
      = List.map (fun D : X.IdealSheafData => D.comap (a ≫ b)) M := by
  induction M with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [← Scheme.IdealSheafData.comap_comp, ih]

private theorem map_comap_congr {X W : Scheme.{u}} {a b : W ⟶ X} (h : a = b)
    (M : List X.IdealSheafData) :
    List.map (fun D : X.IdealSheafData => D.comap a) M
      = List.map (fun D : X.IdealSheafData => D.comap b) M := by
  subst h
  rfl

private theorem sameNontrivialBoundary_of_eq_right {X : Scheme.{u}} {A B B' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) (hB : B = B') : MarkedIdealWithBoundary.SameNontrivialBoundary A B' :=
  hB ▸ h

private theorem isPullback_subschemeMapOfComap_comp_structureMorphism (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (K : Type u) [Field K] (f : T.base →+* K)
    (Z : (T.baseChange K f).scheme.IdealSheafData)
    (hZ : Z = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f)) :
    IsPullback (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩) Z hZ)
      (Z.subschemeι ≫ (T.baseChange K f).structMap)
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      (specMapOfFieldHom T.base K f) := by
  have h2 : IsPullback (fieldBaseChangeProjection T K f) ((T.baseChange K f).structMap) T.structMap
      (specMapOfFieldHom T.base K f) := IsPullback.of_hasPullback _ _
  exact (isPullback_subschemeMapOfComap _ _ (fieldBaseChangeProjection T K f)
    (T.boundary.get ⟨j, hj⟩) Z hZ).paste_vert h2

theorem exists_smooth_surjective_to_restrictToBoundaryDivisor_baseChange (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (hjE : j < E'.length)
    (hget : E'.get ⟨j, hjE⟩ = (T.boundary.get ⟨j, hj⟩).comap (fieldBaseChangeProjection T K f))
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (I₀' : (T.baseChange K f).scheme.IdealSheafData)
    (E₀' : List (T.baseChange K f).scheme.IdealSheafData)
    (hI₀' : I₀' = I₀.comap (fieldBaseChangeProjection T K f))
    (hE₀' : MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E₀'.eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) (E₀.eraseIdx j)))) :
    ∃ (E'' : List ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme.IdealSheafData)
      (e : (E'.get ⟨j, hjE⟩).subscheme ⟶ ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).scheme),
      AlgebraicGeometry.Smooth e ∧
      AlgebraicGeometry.Surjective e ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary E'' ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).boundary ∧
      e ≫ CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
            (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
          divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
            (E'.get ⟨j, hjE⟩) hget ∧
      e ≫ (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').structMap =
          (E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap ∧
      MarkedIdealWithBoundary.SameNontrivialBoundary
        (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
          (List.take (E'.length - 1) (E₀'.eraseIdx j)))
        (List.map (fun D => D.comap e) E'') ∧
      (((T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
            ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
            (I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
              (List.take (E'.length - 1) (E₀'.eraseIdx j)))).IsAdmissible →
          (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').IsAdmissible) ∧
      (((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).withBoundary E'').krullDimSucc =
        ((T.baseChange K f).withSchemeIdealBoundary (E'.get ⟨j, hjE⟩).subscheme
            ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
            (I₀'.comap (E'.get ⟨j, hjE⟩).subschemeι)
            (List.map (fun D => D.comap (E'.get ⟨j, hjE⟩).subschemeι)
              (List.take (E'.length - 1) (E₀'.eraseIdx j)))).krullDimSucc := by
  classical
  subst hI₀'
  have hsq : IsPullback
      (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hget)
      ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
      (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
      (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    isPullback_subschemeMapOfComap_comp_structureMorphism T j hj K f (E'.get ⟨j, hjE⟩) hget
  have hQ : IsPullback
      (CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
        (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f))
      (CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
        (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f))
      (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
      (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨ee, hfst, hsnd, hinv1, hinv2⟩ :
      ∃ ee : _ ≅ _,
        ee.hom ≫ CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
            subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget ∧
          ee.hom ≫ CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) =
            (E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap ∧
          ee.inv ≫ subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget =
            CategoryTheory.Limits.pullback.fst (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) ∧
          ee.inv ≫ ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap) =
            CategoryTheory.Limits.pullback.snd (restrictToBoundaryDivisor T j hj I₀ E₀).structMap
              (specMapOfFieldHom (restrictToBoundaryDivisor T j hj I₀ E₀).base K f) :=
    ⟨hsq.isoIsPullback _ _ hQ, hsq.isoIsPullback_hom_fst _ _ hQ,
      hsq.isoIsPullback_hom_snd _ _ hQ, hsq.isoIsPullback_inv_fst _ _ hQ,
      hsq.isoIsPullback_inv_snd _ _ hQ⟩
  have hlbc : divisorPullbackMap T j hj I₀ E₀ (T.baseChange K f).scheme (fieldBaseChangeProjection T K f)
        (E'.get ⟨j, hjE⟩) hget
      = subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
          (E'.get ⟨j, hjE⟩) hget := rfl
  have hbe := sameNontrivialBoundary_comap_subschemeι (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
      (E'.get ⟨j, hjE⟩) hget (List.take (T.boundary.length - 1) (E₀.eraseIdx j))
      (List.take (E'.length - 1) (E₀'.eraseIdx j)) hE₀'
  refine ⟨List.map (fun D : (E'.get ⟨j, hjE⟩).subscheme.IdealSheafData => D.comap ee.inv)
      (List.map (fun D : (T.baseChange K f).scheme.IdealSheafData =>
        D.comap (E'.get ⟨j, hjE⟩).subschemeι) (List.take (E'.length - 1) (E₀'.eraseIdx j))),
      ee.hom, ?_, ?_, ?_, hfst.trans hlbc.symm, hsnd, ?_, ?_,
      krullDimSucc_eq_of_iso ee.symm⟩
  · exact smooth_of_isIso ee.hom
  · exact surjective_of_isIso ee.hom
  · exact sameNontrivialBoundary_of_eq_right (MarkedIdealWithBoundary.SameNontrivialBoundary.comap ee.inv hbe)
      (((map_comap_map_comap_eq_map_comap_comp ee.inv (subschemeMapOfComap (fieldBaseChangeProjection T K f)
            (T.boundary.get ⟨j, hj⟩) (E'.get ⟨j, hjE⟩) hget) _).trans
          (map_comap_congr hinv1 _)).trans
        (MarkedIdealWithBoundary.baseChange_boundary (restrictToBoundaryDivisor T j hj I₀ E₀) K f).symm)
  · exact sameNontrivialBoundary_of_eq_right (MarkedIdealWithBoundary.SameNontrivialBoundary.refl _)
      (((map_comap_map_comap_eq_map_comap_comp ee.hom ee.inv _).trans
          (map_comap_congr ee.hom_inv_id _)).trans (list_map_comap_id _ _)).symm
  · intro hS
    have hval := isAdmissible_comap_of_iso ee.symm
      ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
      ((I₀.comap (fieldBaseChangeProjection T K f)).comap (E'.get ⟨j, hjE⟩).subschemeι) T.mult
      (List.map (fun D : (T.baseChange K f).scheme.IdealSheafData =>
        D.comap (E'.get ⟨j, hjE⟩).subschemeι) (List.take (E'.length - 1) (E₀'.eraseIdx j))) hS
    have hp : ee.symm.hom ≫ ((E'.get ⟨j, hjE⟩).subschemeι ≫ (T.baseChange K f).structMap)
        = ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).structMap := hinv2
    have s1 : (I₀.comap (fieldBaseChangeProjection T K f)).comap (E'.get ⟨j, hjE⟩).subschemeι
        = (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap
            (subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
              (E'.get ⟨j, hjE⟩) hget) :=
      (comap_subschemeMapOfComap (fieldBaseChangeProjection T K f) (T.boundary.get ⟨j, hj⟩)
        (E'.get ⟨j, hjE⟩) hget I₀).symm
    have hI : ((I₀.comap (fieldBaseChangeProjection T K f)).comap
          (E'.get ⟨j, hjE⟩).subschemeι).comap ee.symm.hom
        = ((restrictToBoundaryDivisor T j hj I₀ E₀).baseChange K f).ideal :=
      (congrArg (fun J : (E'.get ⟨j, hjE⟩).subscheme.IdealSheafData => J.comap ee.symm.hom)
          s1).trans
        (((Scheme.IdealSheafData.comap_comp _ ee.symm.hom _).symm.trans
            (comap_congr hinv1 _)).trans
          (MarkedIdealWithBoundary.baseChange_ideal (restrictToBoundaryDivisor T j hj I₀ E₀) K f).symm)
    exact isAdmissible_congr hp hI rfl rfl hval

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
