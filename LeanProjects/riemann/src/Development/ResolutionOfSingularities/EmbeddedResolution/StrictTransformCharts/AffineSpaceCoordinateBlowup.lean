import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

universe u

def uliftFinset (m : ℕ) (S : Finset (Fin m)) : Finset (ULift.{u} (Fin m)) :=
  S.map ⟨fun j => (ULift.up j : ULift.{u} (Fin m)), fun _ _ h => congrArg ULift.down h⟩

@[simp] theorem mem_uliftFinset {m : ℕ} (S : Finset (Fin m)) (x : ULift.{u} (Fin m)) :
    x ∈ uliftFinset.{u} m S ↔ x.down ∈ S := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp h
    exact ha
  · intro h
    exact Finset.mem_map.mpr ⟨x.down, h, rfl⟩

theorem up_mem_uliftFinset {m : ℕ} {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) :
    (ULift.up j : ULift.{u} (Fin m)) ∈ uliftFinset.{u} m S :=
  (mem_uliftFinset S _).mpr hj

theorem down_mem_of_mem_uliftFinset {m : ℕ} {S : Finset (Fin m)} {x : ULift.{u} (Fin m)}
    (hx : x ∈ uliftFinset.{u} m S) : x.down ∈ S :=
  (mem_uliftFinset S x).mp hx

abbrev finCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Ideal (MvPolynomial (ULift.{u} (Fin m)) k) :=
  coordIdeal k (uliftFinset.{u} m S)

def affineSpaceSpecIso (k : Type u) [Field k] (m : ℕ) :
    affineSpaceFin k m ≅ Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)

private theorem appTop_comp_apply_eq_appTop_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Γ(Z, ⊤)) : (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl

private theorem appTop_specMap_ΓSpecIso_inv_apply {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x)
      = (Scheme.ΓSpecIso S).inv.hom (f.hom x) := by
  have h : (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso S).hom]
    simp [Scheme.ΓSpecIso_naturality]
  have h2 : ((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom x
      = (f ≫ (Scheme.ΓSpecIso S).inv).hom x := by rw [h]
  exact h2

private theorem affineSpaceSpecIso_inv_appTop_coord (k : Type u) [Field k] (m : ℕ)
    (j : ULift.{u} (Fin m)) :
    (affineSpaceSpecIso k m).inv.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) j)
      = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X j) := by
  apply AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord

private theorem affineSpaceSpecIso_hom_appTop_X (k : Type u) [Field k] (m : ℕ)
    (j : ULift.{u} (Fin m)) :
    (affineSpaceSpecIso k m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X j))
      = AffineSpace.coord (Spec (CommRingCat.of k)) j := by
  rw [← affineSpaceSpecIso_inv_appTop_coord k m j, ← appTop_comp_apply_eq_appTop_appTop, Iso.hom_inv_id]
  simp

private theorem affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) :
    (affineSpaceSpecIso k m).inv ≫ affineSpaceFinToSpec k m
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) := by
  simp [affineSpaceSpecIso, affineSpaceFinToSpec]

abbrev affineSpaceCoordBlowup (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) : Scheme.{u} :=
  Blowup.affineBlowup (finCoordIdeal k m S)

def affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    affineSpaceCoordBlowup k m S ⟶ affineSpaceFin k m :=
  Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ (affineSpaceSpecIso k m).inv

private theorem comap_specIdealSheaf_finCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (Blowup.specIdealSheaf (finCoordIdeal k m S)).comap (affineSpaceSpecIso k m).hom
      = coordSubspaceIdeal k m S := by
  have : IsAffine (affineSpaceFin k m) := inferInstance
  have hset : ((affineSpaceSpecIso k m).hom.appTop.hom) ''
      (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom) ''
        ((MvPolynomial.X : ULift.{u} (Fin m) → MvPolynomial (ULift.{u} (Fin m)) k) ''
          (↑(uliftFinset.{u} m S) : Set (ULift.{u} (Fin m)))))
      = (fun i => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (↑S : Set (Fin m)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
      exact ⟨j.down, Finset.mem_coe.mpr (down_mem_of_mem_uliftFinset (Finset.mem_coe.mp hj)),
        (affineSpaceSpecIso_hom_appTop_X k m j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X (ULift.up i)),
        ⟨MvPolynomial.X (ULift.up i),
          ⟨ULift.up i, Finset.mem_coe.mpr (up_mem_uliftFinset (Finset.mem_coe.mp hi)), rfl⟩, rfl⟩,
        ?_⟩
      exact affineSpaceSpecIso_hom_appTop_X k m (ULift.up i)
  have hI : (finCoordIdeal k m S : Ideal (MvPolynomial (ULift.{u} (Fin m)) k))
      = Ideal.span ((MvPolynomial.X : ULift.{u} (Fin m) → MvPolynomial (ULift.{u} (Fin m)) k) ''
          (↑(uliftFinset.{u} m S) : Set (ULift.{u} (Fin m)))) :=
    coordIdeal_eq_span k (uliftFinset.{u} m S)
  rw [Blowup.specIdealSheaf_eq_ofIdealTop, Scheme.IdealSheafData.comap_ofIdealTop, coordSubspaceIdeal_eq_ofIdealTop_span_coord, hI,
    Ideal.map_span, Ideal.map_span, hset]

theorem isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Blowup.IsBlowupAlongIdealSheaf (affineSpaceCoordBlowupMap k m S) (coordSubspaceIdeal k m S) := by
  rw [← comap_specIdealSheaf_finCoordIdeal k m S]
  exact (Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec (finCoordIdeal k m S)).comp_iso_hom
    (affineSpaceSpecIso k m).symm

abbrev finCoordIdealGen (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    ↥(finCoordIdeal k m S) :=
  coordIdealGen k (uliftFinset.{u} m S) (ULift.up s) (up_mem_uliftFinset hs)

abbrev coordBlowupChartRing (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :=
  HomogeneousLocalization.Away (Blowup.reesGrading (finCoordIdeal k m S))
    (Blowup.reesGenerator (finCoordIdeal k m S) (finCoordIdealGen k m S s hs))

def coordBlowupChartRingEquiv (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    coordBlowupChartRing k m S s hs ≃+* MvPolynomial (ULift.{u} (Fin m)) k :=
  @awayCoordGenEquivMvPolynomial k _ (ULift.{u} (Fin m)) (Classical.decEq _) (uliftFinset.{u} m S) (ULift.up s)
    (up_mem_uliftFinset hs)

def coordBlowupChartRingCatIso (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    CommRingCat.of (coordBlowupChartRing k m S s hs) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) :=
  (coordBlowupChartRingEquiv k m S s hs).toCommRingCatIso

def specCoordBlowupChartRingIso (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)) where
  hom := Spec.map (coordBlowupChartRingCatIso k m S s hs).inv
  inv := Spec.map (coordBlowupChartRingCatIso k m S s hs).hom
  hom_inv_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  inv_hom_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

def specCoordBlowupChartRingIsoAffineSpace (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅ affineSpaceFin k m :=
  specCoordBlowupChartRingIso k m S s hs ≪≫ (affineSpaceSpecIso k m).symm

def affineSpaceCoordBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ⟶ affineSpaceCoordBlowup k m S :=
  Blowup.affineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs)

instance instIsOpenImmersionModelBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (hs : s ∈ S) : IsOpenImmersion (affineSpaceCoordBlowupChart k m S s hs) :=
  Blowup.instIsOpenImmersionAffineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs)

private def coordBlowupSubstUliftFin (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] MvPolynomial (ULift.{u} (Fin m)) k :=
  @coordBlowupSubst k _ (ULift.{u} (Fin m)) (Classical.decEq _) (uliftFinset.{u} m S) (ULift.up s)

private theorem specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) :
    Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
        ≫ (affineSpaceSpecIso k m).inv
      = (affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s := by
  refine AffineSpace.hom_ext ?_ ?_
  · show (Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
          ≫ (affineSpaceSpecIso k m).inv) ≫ affineSpaceFinToSpec k m
      = ((affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s) ≫ affineSpaceFinToSpec k m
    rw [Category.assoc, Category.assoc, coordBlowupSubstMap_comp_affineSpaceFinToSpec, affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec,
      ← Spec.map_comp]
    congr 1
    ext r
    simp [coordBlowupSubstUliftFin]
  · intro i
    show (Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
          ≫ (affineSpaceSpecIso k m).inv).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
      = ((affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
    rw [appTop_comp_apply_eq_appTop_appTop, appTop_comp_apply_eq_appTop_appTop, affineSpaceSpecIso_inv_appTop_coord,
      appTop_specMap_ΓSpecIso_inv_apply, coordBlowupSubstMap_appTop_coord]
    by_cases hc : i.down ∈ S ∧ i.down ≠ s
    · rw [if_pos hc, map_mul, affineSpaceSpecIso_inv_appTop_coord, affineSpaceSpecIso_inv_appTop_coord]
      simp [coordBlowupSubstUliftFin, ULift.ext_iff, hc.1, hc.2]
    · rw [if_neg hc, affineSpaceSpecIso_inv_appTop_coord]
      simp [coordBlowupSubstUliftFin, ULift.ext_iff, hc]

theorem affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    affineSpaceCoordBlowupChart k m S s hs ≫ affineSpaceCoordBlowupMap k m S =
      (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s := by
  have hcomp : (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom.comp
      (coordBlowupSubstUliftFin k m S s).toRingHom
      = Blowup.chartRingHom (finCoordIdeal k m S) (finCoordIdealGen k m S s hs) :=
    @awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst k _ (ULift.{u} (Fin m)) (Classical.decEq _)
      (uliftFinset.{u} m S) (ULift.up s) (up_mem_uliftFinset hs)
  have hring : CommRingCat.ofHom (Blowup.chartRingHom (finCoordIdeal k m S) (finCoordIdealGen k m S s hs))
      = CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom ≫
        CommRingCat.ofHom (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom := by
    rw [← hcomp]
    rfl
  show Blowup.affineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs) ≫
      (Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ (affineSpaceSpecIso k m).inv)
    = (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s
  rw [← Category.assoc, Blowup.affineBlowupChart_comp_toSpec, Blowup.algebraMap_chart_eq_chartRingHom, hring,
    Spec.map_comp, Category.assoc, specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv k m S s, ← Category.assoc]
  rfl

theorem iSup_opensRange_affineSpaceCoordBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2))
      = (⊤ : (affineSpaceCoordBlowup k m S).Opens) := by
  refine le_antisymm le_top ?_
  rw [← iSup_opensRange_affineBlowupChart_coordIdealGen k (uliftFinset.{u} m S)]
  refine iSup_le fun j => ?_
  refine le_iSup_of_le ⟨j.1.down, down_mem_of_mem_uliftFinset j.2⟩ ?_
  exact le_rfl

end FunctorialResolution.EmbeddedResolution

end
