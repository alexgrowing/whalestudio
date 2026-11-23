import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

noncomputable def BlowupSequenceData.controlledTransform {X : Scheme.{u}} (d : BlowupSequenceData X)
    (I : X.IdealSheafData) (m : ℕ) : ∀ i : ℕ, (d.obj i).IdealSheafData
  | 0 => I.comap d.isoZero.hom
  | (i + 1) =>
      residualByPow ((d.controlledTransform I m i).comap (d.map i))
        (Blowup.exceptionalIdeal (d.map i) (d.center i)) m

@[simp]
theorem BlowupSequenceData.controlledTransform_zero {X : Scheme.{u}} (d : BlowupSequenceData X)
    (I : X.IdealSheafData) (m : ℕ) :
    d.controlledTransform I m 0 = I.comap d.isoZero.hom := rfl

@[simp]
theorem BlowupSequenceData.controlledTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (I : X.IdealSheafData) (m : ℕ) (i : ℕ) :
    d.controlledTransform I m (i + 1) =
      residualByPow ((d.controlledTransform I m i).comap (d.map i))
        (Blowup.exceptionalIdeal (d.map i) (d.center i)) m := rfl

theorem BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (I : X.IdealSheafData) (m : ℕ) (i : ℕ)
    (h : ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B =
        (d.controlledTransform I m i).comap (d.map i)) :
    Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * d.controlledTransform I m (i + 1) =
      (d.controlledTransform I m i).comap (d.map i) := by
  rw [d.controlledTransform_succ I m i]
  exact pow_mul_residualByPow _ _ m h

noncomputable def BlowupSequenceData.boundaryFrom {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E : List X.IdealSheafData) : ∀ i : ℕ, List (d.obj i).IdealSheafData
  | 0 => E.map (fun D => D.comap d.isoZero.hom)
  | (i + 1) =>
      (d.boundaryFrom E i).map (Blowup.strictTransform (d.map i) (d.center i)) ++
        [Blowup.exceptionalIdeal (d.map i) (d.center i)]

@[simp]
theorem BlowupSequenceData.boundary_zero {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E : List X.IdealSheafData) :
    d.boundaryFrom E 0 = E.map (fun D => D.comap d.isoZero.hom) := rfl

@[simp]
theorem BlowupSequenceData.boundary_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E : List X.IdealSheafData) (i : ℕ) :
    d.boundaryFrom E (i + 1) =
      (d.boundaryFrom E i).map (Blowup.strictTransform (d.map i) (d.center i)) ++
        [Blowup.exceptionalIdeal (d.map i) (d.center i)] := rfl

theorem BlowupSequenceData.boundary_length {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E : List X.IdealSheafData) (i : ℕ) :
    (d.boundaryFrom E i).length = E.length + i := by
  induction i with
  | zero =>
      rw [d.boundary_zero E, List.length_map]
      omega
  | succ j ih =>
      rw [d.boundary_succ E j, List.length_append, List.length_map, ih,
        List.length_cons, List.length_nil]
      omega

structure BlowupSequenceData.IsMarked {k : Type u} [Field k] {X : Scheme.{u}} (d : BlowupSequenceData X)
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) : Prop where
  divisible : ∀ i < d.length, ∃ B : (d.obj (i + 1)).IdealSheafData,
    Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B =
      (d.controlledTransform I m i).comap (d.map i)
  center_order : ∀ i < d.length,
    ((d.center i).support : Set ↥(d.obj i)) ⊆ orderAtLeastLocus (d.controlledTransform I m i) m
  center_smooth : ∀ i < d.length,
    AlgebraicGeometry.Smooth ((d.center i).subschemeι ≫ d.projectionToBase i ≫ p)
  center_snc : ∀ i < d.length,
    HasStrictNormalCrossingsWith (d.projectionToBase i ≫ p) (d.center i) (d.boundaryFrom E i)

noncomputable def BlowupSequenceData.toMarkedBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (d : BlowupSequenceData X) (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) (h : d.IsMarked p I m E) : MarkedBlowupSequenceData p I m E where
  toBlowupSequenceData := d
  proj := d.projectionToBase
  proj_zero := d.projectionToBase_zero
  proj_succ := d.projectionToBase_succ
  ideal := d.controlledTransform I m
  boundary := d.boundaryFrom E
  ideal_zero := rfl
  boundary_zero := rfl
  center_order := h.center_order
  center_smooth := h.center_smooth
  center_snc := h.center_snc
  ideal_succ := fun i hi => d.pow_exceptionalIdeal_mul_controlledTransform_succ I m i (h.divisible i hi)
  boundary_succ := fun i _ => d.boundary_succ E i

section

variable {k : Type u} [Field k] {X : Scheme.{u}} (d : BlowupSequenceData X)
  (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
  (E : List X.IdealSheafData) (h : d.IsMarked p I m E)

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_toBlowupSequenceData :
    (d.toMarkedBlowupSequenceData p I m E h).toBlowupSequenceData = d := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_length :
    (d.toMarkedBlowupSequenceData p I m E h).length = d.length := rfl

theorem BlowupSequenceData.toMarkedBlowupSequenceData_schemeAt (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).obj i = d.obj i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_center (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).center i = d.center i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_blowupMorphism (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).map i = d.map i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_projectionToBase (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).proj i = d.projectionToBase i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_ideal (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).ideal i = d.controlledTransform I m i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_boundary (i : ℕ) :
    (d.toMarkedBlowupSequenceData p I m E h).boundary i = d.boundaryFrom E i := rfl

@[simp]
theorem BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups :
    (d.toMarkedBlowupSequenceData p I m E h).toMarkedSequenceOfBlowups.toSequenceOfBlowups = d.toSequenceOfBlowups :=
  MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups _

end

private theorem le_of_span_singleton_mul_eq_mul {R : Type u} [CommRing R] {f : R}
    (hf : f ∈ nonZeroDivisors R) {I J : Ideal R}
    (h : Ideal.span ({f} : Set R) * I = Ideal.span ({f} : Set R) * J) : I ≤ J := by
  intro a ha
  have h1 : f * a ∈ Ideal.span ({f} : Set R) * J := by
    rw [← h]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) ha
  obtain ⟨z, hz, hfz⟩ := Ideal.mem_span_singleton_mul.mp h1
  have hza : a = z := ((mul_cancel_left_mem_nonZeroDivisors hf).mp hfz).symm
  rw [hza]
  exact hz

private theorem eq_of_span_singleton_mul_eq_mul {R : Type u} [CommRing R] {f : R}
    (hf : f ∈ nonZeroDivisors R) {I J : Ideal R}
    (h : Ideal.span ({f} : Set R) * I = Ideal.span ({f} : Set R) * J) : I = J :=
  le_antisymm (le_of_span_singleton_mul_eq_mul hf h) (le_of_span_singleton_mul_eq_mul hf h.symm)

private theorem stalkIdeal_eq_of_mul_eq_mul {Y : Scheme.{u}} {F A B : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (h : F * A = F * B) (x : ↥Y) :
    stalkIdeal A x = stalkIdeal B x := by
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  let _ : Algebra ↑(Y.presheaf.obj (Opposite.op (U : Y.Opens))) ↑(Y.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨x, hxU⟩ : ↥(U : Y.Opens))
  have : IsLocalization
      (IsAffineOpen.primeIdealOf U.2 (⟨x, hxU⟩ : ↥(U : Y.Opens))).asIdeal.primeCompl
      ↑(Y.presheaf.stalk x) :=
    IsAffineOpen.isLocalization_stalk U.2 (⟨x, hxU⟩ : ↥(U : Y.Opens))
  have hnzd : (CommRingCat.Hom.hom (Y.presheaf.germ (U : Y.Opens) x hxU)) f ∈
      nonZeroDivisors ↑(Y.presheaf.stalk x) :=
    IsLocalization.map_nonZeroDivisors_le
      (IsAffineOpen.primeIdealOf U.2 (⟨x, hxU⟩ : ↥(U : Y.Opens))).asIdeal.primeCompl
      ↑(Y.presheaf.stalk x) ⟨f, hf, rfl⟩
  have hstalk : stalkIdeal F x =
      Ideal.span ({(CommRingCat.Hom.hom (Y.presheaf.germ (U : Y.Opens) x hxU)) f} :
        Set ↑(Y.presheaf.stalk x)) := by
    rw [stalkIdeal_eq_map_germ F x U hxU, hFU, Ideal.map_span, Set.image_singleton]
  have hmul : stalkIdeal F x * stalkIdeal A x = stalkIdeal F x * stalkIdeal B x := by
    rw [← stalkIdeal_mul, ← stalkIdeal_mul, h]
  rw [hstalk] at hmul
  exact eq_of_span_singleton_mul_eq_mul hnzd hmul

private theorem eq_of_stalkIdeal_eq {Y : Scheme.{u}} {A B : Y.IdealSheafData}
    (h : ∀ x : ↥Y, stalkIdeal A x = stalkIdeal B x) : A = B := by
  apply Scheme.IdealSheafData.ext
  funext V
  apply Ideal.eq_of_localization_maximal
  intro P hP
  have : P.IsPrime := hP.isPrime
  have hx : IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) ∈ (V : Y.Opens) := by
    have hr : IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) ∈
        Set.range (IsAffineOpen.fromSpec V.2) := Set.mem_range_self _
    rw [IsAffineOpen.range_fromSpec V.2] at hr
    exact hr
  let _ : Algebra ↑(Y.presheaf.obj (Opposite.op (V : Y.Opens)))
      ↑(Y.presheaf.stalk (IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _))) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf
      (⟨IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _), hx⟩ : ↥(V : Y.Opens))
  have : IsLocalization P.primeCompl
      ↑(Y.presheaf.stalk (IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _))) :=
    IsAffineOpen.isLocalization_stalk' V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _) hx
  have key := h (IsAffineOpen.fromSpec V.2 (⟨P, hP.isPrime⟩ : PrimeSpectrum _))
  rw [stalkIdeal_eq_map_germ A _ V hx, stalkIdeal_eq_map_germ B _ V hx] at key
  exact IsLocalization.map_eq_map_of_map_eq_map P.primeCompl key

theorem isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal {X' X : Scheme.{u}} {f : X' ⟶ X}
    {Z : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf f Z) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal f Z) := by
  rw [Blowup.exceptionalIdeal_eq_comap]
  exact Blowup.IsBlowupAlongIdealSheaf.isLocallyGeneratedByNonZeroDivisor_comap h

theorem isLocallyGeneratedByNonZeroDivisor_pow {Y : Scheme.{u}} {F : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (m : ℕ) : Blowup.IsLocallyGeneratedByNonZeroDivisor (F ^ m) := by
  intro x
  obtain ⟨U, f, hxU, hf, hFU⟩ := hF x
  refine ⟨U, f ^ m, hxU, pow_mem hf m, ?_⟩
  rw [Scheme.IdealSheafData.ideal_pow]
  show F.ideal U ^ m = _
  rw [hFU, Ideal.span_singleton_pow]

theorem eq_of_isLocallyGeneratedByNonZeroDivisor_mul_eq_mul {Y : Scheme.{u}} {F A B : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (h : F * A = F * B) : A = B :=
  eq_of_stalkIdeal_eq (stalkIdeal_eq_of_mul_eq_mul hF h)

theorem eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul {Y : Scheme.{u}} {F A B : Y.IdealSheafData}
    (hF : Blowup.IsLocallyGeneratedByNonZeroDivisor F) (m : ℕ) (h : F ^ m * A = F ^ m * B) : A = B :=
  eq_of_isLocallyGeneratedByNonZeroDivisor_mul_eq_mul (isLocallyGeneratedByNonZeroDivisor_pow hF m) h

theorem BlowupSequenceData.eq_of_pow_exceptionalIdeal_mul_eq_mul {X : Scheme.{u}} (d : BlowupSequenceData X)
    {i : ℕ} (hi : i < d.length) (m : ℕ) (A B : (d.obj (i + 1)).IdealSheafData)
    (h : Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * A =
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B) : A = B :=
  eq_of_isLocallyGeneratedByNonZeroDivisor_pow_mul_eq_mul
    (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (d.isBlowup i hi)) m h

namespace MarkedBlowupSequenceData

theorem projectionToBase_eq_toBlowupSequenceData_projectionToBase {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    s.proj i = s.toBlowupSequenceData.projectionToBase i := by
  induction i with
  | zero => rw [s.proj_zero, s.toBlowupSequenceData.projectionToBase_zero]
  | succ j ih => rw [s.proj_succ j, s.toBlowupSequenceData.projectionToBase_succ j, ih]

theorem controlledTransform_and_boundary_eq_of_cancel {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)
    (huniq : ∀ i < s.length, ∀ A B : (s.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (s.map i) (s.center i) ^ m * A = (s.ideal i).comap (s.map i) →
      Blowup.exceptionalIdeal (s.map i) (s.center i) ^ m * B = (s.ideal i).comap (s.map i) →
      A = B)
    (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i ∧
      s.toBlowupSequenceData.boundaryFrom E i = s.boundary i := by
  revert hi
  induction i with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [BlowupSequenceData.controlledTransform_zero]
        exact s.ideal_zero.symm
      · rw [BlowupSequenceData.boundary_zero]
        exact s.boundary_zero.symm
  | succ j ih =>
      intro hi
      have hj : j < s.length := hi
      obtain ⟨ih1, ih2⟩ := ih (le_of_lt hj)
      refine ⟨?_, ?_⟩
      · rw [BlowupSequenceData.controlledTransform_succ, ih1]
        have hex : ∃ B : (s.obj (j + 1)).IdealSheafData,
            Blowup.exceptionalIdeal (s.map j) (s.center j) ^ m * B =
              (s.ideal j).comap (s.map j) :=
          ⟨s.ideal (j + 1), s.ideal_succ j hj⟩
        exact huniq j hj _ _ (pow_mul_residualByPow _ _ m hex) (s.ideal_succ j hj)
      · rw [BlowupSequenceData.boundary_succ, ih2]
        exact (s.boundary_succ j hj).symm

theorem controlledTransform_and_boundary_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)
    (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i ∧
      s.toBlowupSequenceData.boundaryFrom E i = s.boundary i :=
  s.controlledTransform_and_boundary_eq_of_cancel
    (fun _j hj A B hA hB =>
      s.toBlowupSequenceData.eq_of_pow_exceptionalIdeal_mul_eq_mul hj m A B (hA.trans hB.symm))
    i hi

theorem toBlowupSequenceData_controlledTransform_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)
    (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.controlledTransform I m i = s.ideal i :=
  (s.controlledTransform_and_boundary_eq i hi).1

theorem toBlowupSequenceData_boundary_eq_boundary_of_le {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E)
    (i : ℕ) (hi : i ≤ s.length) :
    s.toBlowupSequenceData.boundaryFrom E i = s.boundary i :=
  (s.controlledTransform_and_boundary_eq i hi).2

theorem isMarked_toBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedBlowupSequenceData p I m E) :
    s.toBlowupSequenceData.IsMarked p I m E := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨s.ideal (i + 1), ?_⟩
    rw [s.toBlowupSequenceData_controlledTransform_eq i (le_of_lt hi)]
    exact s.ideal_succ i hi
  · intro i hi
    rw [s.toBlowupSequenceData_controlledTransform_eq i (le_of_lt hi)]
    exact s.center_order i hi
  · intro i hi
    have h := s.center_smooth i hi
    rw [s.projectionToBase_eq_toBlowupSequenceData_projectionToBase i] at h
    exact h
  · intro i hi
    have h := s.center_snc i hi
    rw [s.projectionToBase_eq_toBlowupSequenceData_projectionToBase i] at h
    rw [s.toBlowupSequenceData_boundary_eq_boundary_of_le i (le_of_lt hi)]
    exact h

theorem ofMarkedSequence_controlledTransform {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E)
    (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.controlledTransform I m i = s.ideal i :=
  (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData_controlledTransform_eq i hi

theorem ofMarkedSequence_boundary {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E)
    (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.boundaryFrom E i = s.boundary i :=
  (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData_boundary_eq_boundary_of_le i hi

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution
