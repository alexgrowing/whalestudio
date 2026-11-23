import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

open Classical in
noncomputable def residualByPow {Y : Scheme.{u}} (A F : Y.IdealSheafData) (m : ℕ) : Y.IdealSheafData :=
  if h : ∃ B : Y.IdealSheafData, F ^ m * B = A then h.choose else ⊤

theorem pow_mul_residualByPow {Y : Scheme.{u}} (A F : Y.IdealSheafData) (m : ℕ)
    (h : ∃ B : Y.IdealSheafData, F ^ m * B = A) : F ^ m * residualByPow A F m = A := by
  have hx : residualByPow A F m = h.choose := dif_pos h
  rw [hx]
  exact h.choose_spec

private theorem map_comap_id_list_idealSheafData {X : Scheme.{u}} (E : List X.IdealSheafData) :
    E.map (fun D => D.comap (𝟙 X)) = E := by
  induction E with
  | nil => rfl
  | cons a t ih => simp [Scheme.IdealSheafData.comap_id]

@[simp]
theorem exceptionalIdeal_id {X : Scheme.{u}} (Z : X.IdealSheafData) :
    Blowup.exceptionalIdeal (𝟙 X) Z = Z := by
  rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]

private def singleBlowupScheme {X : Scheme.{u}} (Z : X.IdealSheafData) : ℕ → Scheme.{u}
  | 0 => X
  | (_ + 1) => Blowup.blowup Z

private def singleBlowupMap {X : Scheme.{u}} (Z : X.IdealSheafData) :
    ∀ i : ℕ, singleBlowupScheme Z (i + 1) ⟶ singleBlowupScheme Z i
  | 0 => Blowup.blowup.proj Z
  | (_ + 1) => 𝟙 (Blowup.blowup Z)

private def singleBlowupCenter {X : Scheme.{u}} (Z : X.IdealSheafData) :
    ∀ i : ℕ, (singleBlowupScheme Z i).IdealSheafData
  | 0 => Z
  | (_ + 1) => ⊤

private def singleBlowupProj {X : Scheme.{u}} (Z : X.IdealSheafData) : ∀ i : ℕ, singleBlowupScheme Z i ⟶ X
  | 0 => 𝟙 X
  | (_ + 1) => Blowup.blowup.proj Z

private def singleBlowupResidualIdeal {X : Scheme.{u}} (I Z : X.IdealSheafData) (m : ℕ) :
    ∀ i : ℕ, (singleBlowupScheme Z i).IdealSheafData
  | 0 => I.comap (𝟙 X)
  | (_ + 1) => residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m

private def singleBlowupBoundary {X : Scheme.{u}} (Z : X.IdealSheafData) (E : List X.IdealSheafData) :
    ∀ i : ℕ, List (singleBlowupScheme Z i).IdealSheafData
  | 0 => E.map (fun D => D.comap (𝟙 X))
  | (_ + 1) =>
      E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z]

private theorem isBlowupAlongIdealSheaf_singleBlowupMap {X : Scheme.{u}} (Z : X.IdealSheafData) (i : ℕ) (hi : i < 1) :
    Blowup.IsBlowupAlongIdealSheaf (singleBlowupMap Z i) (singleBlowupCenter Z i) := by
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show Blowup.IsBlowupAlongIdealSheaf (Blowup.blowup.proj Z) Z
  exact Blowup.blowup.isBlowupAlongIdealSheaf_proj Z

private def singleBlowupSequenceData {X : Scheme.{u}} (Z : X.IdealSheafData) : BlowupSequenceData X where
  length := 1
  obj := singleBlowupScheme Z
  map := singleBlowupMap Z
  isoZero := Iso.refl X
  center := singleBlowupCenter Z
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_singleBlowupMap Z i hi

private theorem singleBlowupProj_succ {X : Scheme.{u}} (Z : X.IdealSheafData) (i : ℕ) :
    singleBlowupProj Z (i + 1) = singleBlowupMap Z i ≫ singleBlowupProj Z i := by
  cases i with
  | zero =>
      show Blowup.blowup.proj Z = Blowup.blowup.proj Z ≫ 𝟙 X
      exact (Category.comp_id _).symm
  | succ j =>
      show Blowup.blowup.proj Z = 𝟙 (Blowup.blowup Z) ≫ Blowup.blowup.proj Z
      exact (Category.id_comp _).symm

private theorem singleBlowupCenter_support_subset_orderAtLeastLocus {X : Scheme.{u}} (I Z : X.IdealSheafData) (m : ℕ)
    (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m) :
    ∀ i : ℕ, i < 1 →
      ((singleBlowupCenter Z i).support : Set ↥(singleBlowupScheme Z i)) ⊆ orderAtLeastLocus (singleBlowupResidualIdeal I Z m i) m := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show (Z.support : Set ↥X) ⊆ orderAtLeastLocus (I.comap (𝟙 X)) m
  rw [Scheme.IdealSheafData.comap_id]
  exact hord

private theorem smooth_singleBlowupCenter_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} (Z : X.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)) :
    ∀ i : ℕ, i < 1 →
      AlgebraicGeometry.Smooth ((singleBlowupCenter Z i).subschemeι ≫ singleBlowupProj Z i ≫ p) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show AlgebraicGeometry.Smooth (Z.subschemeι ≫ 𝟙 X ≫ p)
  rw [Category.id_comp]
  exact hsm

private theorem hasStrictNormalCrossingsWith_singleBlowupCenter {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z E) :
    ∀ i : ℕ, i < 1 →
      HasStrictNormalCrossingsWith (singleBlowupProj Z i ≫ p) (singleBlowupCenter Z i) (singleBlowupBoundary Z E i) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show HasStrictNormalCrossingsWith (𝟙 X ≫ p) Z (E.map (fun D => D.comap (𝟙 X)))
  rw [map_comap_id_list_idealSheafData E, Category.id_comp]
  exact hsnc

private theorem exceptionalIdeal_pow_mul_singleBlowupResidualIdeal_succ {X : Scheme.{u}} (I Z : X.IdealSheafData) (m : ℕ)
    (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
      (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z)) :
    ∀ i : ℕ, i < 1 →
      Blowup.exceptionalIdeal (singleBlowupMap Z i) (singleBlowupCenter Z i) ^ m * singleBlowupResidualIdeal I Z m (i + 1) =
        (singleBlowupResidualIdeal I Z m i).comap (singleBlowupMap Z i) := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z ^ m *
      residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m =
    (I.comap (𝟙 X)).comap (Blowup.blowup.proj Z)
  rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact pow_mul_residualByPow _ _ _ hdiv

private theorem singleBlowupBoundary_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    ∀ i : ℕ, i < 1 →
      singleBlowupBoundary Z E (i + 1) =
        (singleBlowupBoundary Z E i).map (Blowup.strictTransform (singleBlowupMap Z i) (singleBlowupCenter Z i)) ++
          [Blowup.exceptionalIdeal (singleBlowupMap Z i) (singleBlowupCenter Z i)] := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  show E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z] =
      (E.map (fun D => D.comap (𝟙 X))).map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++
        [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z]
  rw [map_comap_id_list_idealSheafData E]

namespace MarkedBlowupSequenceData

def ofSingleBlowup {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (Z : X.IdealSheafData)
    (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p))
    (hsnc : HasStrictNormalCrossingsWith p Z E)
    (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m)
    (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
      (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z)) :
    MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := singleBlowupSequenceData Z
  proj := singleBlowupProj Z
  proj_zero := rfl
  proj_succ := fun i => singleBlowupProj_succ Z i
  ideal := singleBlowupResidualIdeal I Z m
  boundary := singleBlowupBoundary Z E
  ideal_zero := rfl
  boundary_zero := rfl
  center_order := singleBlowupCenter_support_subset_orderAtLeastLocus I Z m hord
  center_smooth := smooth_singleBlowupCenter_of_smooth Z hsm
  center_snc := hasStrictNormalCrossingsWith_singleBlowupCenter Z E hsnc
  ideal_succ := exceptionalIdeal_pow_mul_singleBlowupResidualIdeal_succ I Z m hdiv
  boundary_succ := singleBlowupBoundary_succ Z E

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {Z : X.IdealSheafData}
  (hsm : AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)) (hsnc : HasStrictNormalCrossingsWith p Z E)
  (hord : (Z.support : Set ↥X) ⊆ orderAtLeastLocus I m)
  (hdiv : ∃ B : (Blowup.blowup Z).IdealSheafData,
    (Z.comap (Blowup.blowup.proj Z)) ^ m * B = I.comap (Blowup.blowup.proj Z))

@[simp]
theorem ofSingleBlowup_length :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.length = 1 := rfl

@[simp]
theorem ofSingleBlowup_schemeAt_succ (i : ℕ) :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.obj (i + 1) = Blowup.blowup Z := rfl

theorem ofSingleBlowup_schemeAt_zero :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.obj 0 = X := rfl

theorem ofSingleBlowup_blowupMorphism_zero :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.map 0 = Blowup.blowup.proj Z := rfl

theorem ofSingleBlowup_projectionToBase_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).proj 1 = Blowup.blowup.proj Z := rfl

theorem ofSingleBlowup_center_zero :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).toBlowupSequenceData.center 0 = Z := rfl

theorem ofSingleBlowup_ideal_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).ideal 1 =
      residualByPow (I.comap (Blowup.blowup.proj Z)) (Z.comap (Blowup.blowup.proj Z)) m := rfl

theorem ofSingleBlowup_boundary_one :
    (ofSingleBlowup p I m E Z hsm hsnc hord hdiv).boundary 1 =
      E.map (Blowup.strictTransform (Blowup.blowup.proj Z) Z) ++ [Blowup.exceptionalIdeal (Blowup.blowup.proj Z) Z] := rfl

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution
