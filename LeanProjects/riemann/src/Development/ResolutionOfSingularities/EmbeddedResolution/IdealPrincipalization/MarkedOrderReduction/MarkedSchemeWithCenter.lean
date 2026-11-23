import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure MarkedSchemeWithCenter (k : Type u) [Field k] where
  ambient : Scheme.{u}
  ideal : ambient.IdealSheafData
  boundary : List ambient.IdealSheafData
  structMap : ambient ⟶ Spec (CommRingCat.of k)
  center : ambient.IdealSheafData

private theorem comap_inv_comap_hom {X Y : Scheme.{u}} (e : X ≅ Y) (I : Y.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id]
  simp

namespace MarkedSchemeWithCenter

variable {k : Type u} [Field k]

def transport (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) : MarkedSchemeWithCenter k where
  ambient := A
  ideal := D.ideal.comap e.hom
  boundary := D.boundary.map (fun J => J.comap e.hom)
  structMap := e.hom ≫ D.structMap
  center := D.center.comap e.hom

@[simp]
theorem transport_ambient (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).ambient = A := rfl

@[simp]
theorem transport_ideal (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).ideal = D.ideal.comap e.hom := rfl

@[simp]
theorem transport_boundary (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).boundary = D.boundary.map (fun J => J.comap e.hom) := rfl

@[simp]
theorem transport_projectionToBase (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).structMap = e.hom ≫ D.structMap := rfl

@[simp]
theorem transport_center (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (e : A ≅ D.ambient) :
    (D.transport e).center = D.center.comap e.hom := rfl

private theorem mk_congr {K : Type u} [Field K] (A : Scheme.{u})
    (I I' : A.IdealSheafData) (B B' : List A.IdealSheafData)
    (f f' : A ⟶ Spec (CommRingCat.of K)) (C C' : A.IdealSheafData)
    (h1 : I = I') (h2 : B = B') (h3 : f = f') (h4 : C = C') :
    (MarkedSchemeWithCenter.mk A I B f C : MarkedSchemeWithCenter K) = MarkedSchemeWithCenter.mk A I' B' f' C' := by
  subst h1 h2 h3 h4
  rfl

theorem transport_refl (D : MarkedSchemeWithCenter k) : D.transport (Iso.refl D.ambient) = D := by
  obtain ⟨A, I, B, f, C⟩ := D
  have h1 : I.comap (𝟙 A) = I := by simp
  have h2 : B.map (fun J => J.comap (𝟙 A)) = B := by simp
  have h3 : 𝟙 A ≫ f = f := Category.id_comp f
  have h4 : C.comap (𝟙 A) = C := by simp
  exact mk_congr _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

end MarkedSchemeWithCenter

def IsInvariantUnderIso {k : Type u} [Field k] (P : MarkedSchemeWithCenter.{u} k → Prop) : Prop :=
  ∀ (D : MarkedSchemeWithCenter.{u} k) (A : Scheme.{u}) (e : A ≅ D.ambient), P D → P (D.transport e)

namespace MarkedBlowupSequenceData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

def dataAt (s : MarkedBlowupSequenceData p I m E) (i : ℕ) : MarkedSchemeWithCenter.{u} k where
  ambient := s.toBlowupSequenceData.obj i
  ideal := s.ideal i
  boundary := s.boundary i
  structMap := s.proj i ≫ p
  center := s.toBlowupSequenceData.center i

@[simp]
theorem dataAt_ambient (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).ambient = s.toBlowupSequenceData.obj i := rfl

@[simp]
theorem dataAt_ideal (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).ideal = s.ideal i := rfl

@[simp]
theorem dataAt_boundary (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).boundary = s.boundary i := rfl

@[simp]
theorem dataAt_structMap (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).structMap = s.proj i ≫ p := rfl

@[simp]
theorem dataAt_center (s : MarkedBlowupSequenceData p I m E) (i : ℕ) :
    (s.dataAt i).center = s.toBlowupSequenceData.center i := rfl

private theorem transport_dataAt_congr {K : Type u} [Field K] {Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of K)} {J : Y.IdealSheafData} {n : ℕ}
    {F : List Y.IdealSheafData} (d : MarkedBlowupSequenceData q J n F) {a b : ℕ} (hab : a = b)
    {Z : Scheme.{u}} (h1 : Z = d.toBlowupSequenceData.obj a) (h2 : Z = d.toBlowupSequenceData.obj b) :
    (d.dataAt a).transport (eqToIso h1) = (d.dataAt b).transport (eqToIso h2) := by
  subst hab
  rfl

variable (s : MarkedBlowupSequenceData p I m E)
  (t : MarkedBlowupSequenceData (s.proj s.toBlowupSequenceData.length ≫ p) (s.ideal s.toBlowupSequenceData.length) m
    (s.boundary s.toBlowupSequenceData.length))

theorem append_dataAt_of_lt_length (hinv : ComapIsoInvariance.{u}) {i : ℕ} (h : i < s.toBlowupSequenceData.length) :
    (s.append t hinv).dataAt i =
      (s.dataAt i).transport (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_of_lt h))) := by
  have hle : i ≤ s.toBlowupSequenceData.length := le_of_lt h
  have h1 : s.appendIdeal t i =
      (s.ideal i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle)) :=
    appendIdeal_of_le_length s t hle
  have h2 : s.appendBoundary t i =
      (s.boundary i).map (fun J => J.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle))) :=
    appendBoundary_of_le_length s t hle
  have h3 : s.appendProjectionToBase t i ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle) ≫ (s.proj i ≫ p) := by
    rw [appendProjectionToBase_of_le_length s t hle, Category.assoc]
  have h4 : (s.appendToBlowupSequenceData t).center i =
      (s.toBlowupSequenceData.center i).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t hle)) :=
    appendToBlowupSequenceData_center_of_lt_length s t h
  exact MarkedSchemeWithCenter.mk_congr _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

theorem append_dataAt_length (hinv : ComapIsoInvariance.{u}) :
    (s.append t hinv).dataAt s.toBlowupSequenceData.length =
      ((t.dataAt 0).transport t.toBlowupSequenceData.isoZero.symm).transport
        (eqToIso (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) := by
  have h1 : s.appendIdeal t s.toBlowupSequenceData.length =
      ((t.ideal 0).comap t.toBlowupSequenceData.isoZero.inv).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) := by
    rw [appendIdeal_of_le_length s t (le_refl s.toBlowupSequenceData.length), t.ideal_zero, comap_inv_comap_hom]
  have h2 : s.appendBoundary t s.toBlowupSequenceData.length =
      ((t.boundary 0).map (fun J => J.comap t.toBlowupSequenceData.isoZero.inv)).map
        (fun J => J.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)))) := by
    rw [appendBoundary_of_le_length s t (le_refl s.toBlowupSequenceData.length), t.boundary_zero]
    simp only [List.map_map, Function.comp_def, comap_inv_comap_hom]
  have h3 : s.appendProjectionToBase t s.toBlowupSequenceData.length ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length)) ≫
        (t.toBlowupSequenceData.isoZero.inv ≫
          (t.proj 0 ≫ (s.proj s.toBlowupSequenceData.length ≫ p))) := by
    rw [appendProjectionToBase_of_le_length s t (le_refl s.toBlowupSequenceData.length), t.proj_zero]
    simp
  have h4 : (s.appendToBlowupSequenceData t).center s.toBlowupSequenceData.length =
      ((t.toBlowupSequenceData.center 0).comap t.toBlowupSequenceData.isoZero.inv).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_le_length s t (le_refl s.toBlowupSequenceData.length))) :=
    appendToBlowupSequenceData_center_length s t
  exact MarkedSchemeWithCenter.mk_congr _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

theorem append_dataAt_of_length_lt (hinv : ComapIsoInvariance.{u}) {i : ℕ} (h : s.toBlowupSequenceData.length < i) :
    (s.append t hinv).dataAt i =
      (t.dataAt (i - s.toBlowupSequenceData.length)).transport
        (eqToIso (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) := by
  have h1 : s.appendIdeal t i =
      (t.ideal (i - s.toBlowupSequenceData.length)).comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) :=
    appendIdeal_of_length_lt s t h
  have h2 : s.appendBoundary t i =
      (t.boundary (i - s.toBlowupSequenceData.length)).map
        (fun J => J.comap (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h))) :=
    appendBoundary_of_length_lt s t h
  have h3 : s.appendProjectionToBase t i ≫ p =
      eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h) ≫
        (t.proj (i - s.toBlowupSequenceData.length) ≫ (s.proj s.toBlowupSequenceData.length ≫ p)) := by
    rw [appendProjectionToBase_of_length_lt s t h]
    simp only [Category.assoc]
  have h4 : (s.appendToBlowupSequenceData t).center i =
      (t.toBlowupSequenceData.center (i - s.toBlowupSequenceData.length)).comap
        (eqToHom (appendToBlowupSequenceData_schemeAt_of_length_lt s t h)) :=
    appendToBlowupSequenceData_center_of_length_lt s t h
  exact MarkedSchemeWithCenter.mk_congr _ _ _ _ _ _ _ _ _ h1 h2 h3 h4

theorem append_dataAt_last (hinv : ComapIsoInvariance.{u}) (h : 0 < t.toBlowupSequenceData.length) :
    (s.append t hinv).dataAt ((s.append t hinv).toBlowupSequenceData.length) =
      (t.dataAt t.toBlowupSequenceData.length).transport
        (eqToIso (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
  have hgt : s.toBlowupSequenceData.length < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := by omega
  have key : (s.append t hinv).dataAt (s.toBlowupSequenceData.length + t.toBlowupSequenceData.length) =
      (t.dataAt t.toBlowupSequenceData.length).transport
        (eqToIso (appendToBlowupSequenceData_schemeAt_length_add_length s t h)) := by
    rw [append_dataAt_of_length_lt s t hinv hgt]
    exact transport_dataAt_congr t (by omega) _ _
  exact key

theorem append_dataAt_of_forall (hinv : ComapIsoInvariance.{u}) (P : MarkedSchemeWithCenter.{u} k → Prop)
    (hP : IsInvariantUnderIso P)
    (hs : ∀ i < s.toBlowupSequenceData.length, P (s.dataAt i))
    (ht : ∀ i < t.toBlowupSequenceData.length, P (t.dataAt i))
    (i : ℕ) (hi : i < (s.append t hinv).toBlowupSequenceData.length) :
    P ((s.append t hinv).dataAt i) := by
  have hN : i < s.toBlowupSequenceData.length + t.toBlowupSequenceData.length := hi
  rcases lt_trichotomy i s.toBlowupSequenceData.length with hlt | heq | hgt
  · rw [append_dataAt_of_lt_length s t hinv hlt]
    exact hP (s.dataAt i) _ _ (hs i hlt)
  · subst heq
    rw [append_dataAt_length s t hinv]
    exact hP _ _ _ (hP (t.dataAt 0) _ _ (ht 0 (by omega)))
  · rw [append_dataAt_of_length_lt s t hinv hgt]
    exact hP (t.dataAt (i - s.toBlowupSequenceData.length)) _ _
      (ht (i - s.toBlowupSequenceData.length) (by omega))

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution

end
