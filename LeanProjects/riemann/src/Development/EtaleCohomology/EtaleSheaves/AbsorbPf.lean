import Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits.ColimOf

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.AbsorbPf

def Sys : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (φ : ∀ j, D.obj j →+* Ω),
    (∀ j, Et (t.app j)) ∧ (∀ j, (φ j).comp (t.app j).hom = ι) ∧
    (∀ (j k : J) (a : j ⟶ k), (φ k).comp (D.map a).hom = φ j) ∧
    (∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = ι →
      ∃ (j : J) (h : B ⟶ D.obj j), g ≫ h = t.app j ∧ (φ j).comp h.hom = φB) ∧
    (∀ (j : J) (x : D.obj j), φ j x ≠ 0 → ∃ (k : J) (a : j ⟶ k), IsUnit ((D.map a).hom x))

theorem t_nat {J : Type} [SmallCategory J] {A : CommRingCat.{0}} {D : J ⥤ CommRingCat.{0}}
    (t : (Functor.const J).obj A ⟶ D) {j k : J} (a : j ⟶ k) : t.app j ≫ D.map a = t.app k := by
  have := t.naturality a
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
  exact this.symm

theorem Absorb_of (hS : Sys) : LateralTheory.E.ColimPf.Absorb := by
  intro A Ω _ ι
  obtain ⟨J, _, _, D, t, φ, hEt, hpt, hcomp, habs, hloc⟩ := hS A Ω ι
  let O : CommRingCat.{0} := colimit D
  let s : D ⟶ (Functor.const J).obj O := (colimit.cocone D).ι
  let j0 : J := IsFiltered.nonempty.some
  let f : A ⟶ O := t.app j0 ≫ colimit.ι D j0
  have hf : ∀ j, t.app j ≫ colimit.ι D j = f := by
    intro j
    let k := IsFiltered.max j j0
    show t.app j ≫ colimit.ι D j = t.app j0 ≫ colimit.ι D j0
    rw [← colimit.w D (IsFiltered.leftToMax j j0), ← colimit.w D (IsFiltered.rightToMax j j0),
      ← Category.assoc, ← Category.assoc, t_nat, t_nat]
  let cΩ : Cocone D :=
    { pt := CommRingCat.of Ω
      ι := { app := fun j => CommRingCat.ofHom (φ j)
             naturality := by
               intro j k a
               ext x
               have := DFunLike.congr_fun (hcomp j k a) x
               simpa using this } }
  let ψ : O →+* Ω := (colimit.desc D cΩ).hom
  have hψ : ∀ j (y : D.obj j), ψ (colimit.ι D j y) = φ j y := by
    intro j y
    have := colimit.ι_desc cΩ j
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom this) y
  refine ⟨O, f, ψ, ?_, ?_, ?_, ?_⟩
  · refine ⟨J, inferInstance, inferInstance, D, t, s, colimit.isColimit D, fun j => ⟨hEt j, hf j⟩⟩
  · ext a
    have := DFunLike.congr_fun (hpt j0) a
    simp only [RingHom.comp_apply] at this ⊢
    rw [← this, ← hψ]; rfl
  · intro x hx
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep D x
    rw [hψ] at hx
    obtain ⟨k, a, hu⟩ := hloc j y hx
    have : colimit.ι D j y = colimit.ι D k ((D.map a).hom y) := by
      rw [← colimit.w D a]; rfl
    rw [this]
    exact hu.map (colimit.ι D k).hom
  · intro B g hg φB hφB
    obtain ⟨j, h, hh1, hh2⟩ := habs B g hg φB hφB
    refine ⟨h ≫ colimit.ι D j, ?_, ?_⟩
    · rw [← Category.assoc, hh1, hf]
    · ext b
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      rw [hψ]
      exact DFunLike.congr_fun hh2 b

def Sys2 : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (φ : ∀ j, D.obj j →+* Ω),
    (∀ j, Et (t.app j)) ∧ (∀ j, (φ j).comp (t.app j).hom = ι) ∧
    (∀ (j k : J) (a : j ⟶ k), (φ k).comp (D.map a).hom = φ j) ∧
    (∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = ι →
      ∃ (j : J) (h : B ⟶ D.obj j), g ≫ h = t.app j ∧ (φ j).comp h.hom = φB) ∧
    (∀ (j : J) (B : CommRingCat.{0}) (g : D.obj j ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = φ j →
      ∃ (k : J) (a : j ⟶ k) (h : B ⟶ D.obj k), g ≫ h = D.map a)

theorem Sys_of (h2 : Sys2) : Sys := by
  intro A Ω _ ι
  obtain ⟨J, i1, i2, D, t, φ, hEt, hpt, hcomp, habs, hst⟩ := h2 A Ω ι
  refine ⟨J, i1, i2, D, t, φ, hEt, hpt, hcomp, habs, ?_⟩
  intro j x hx
  let B : CommRingCat.{0} := CommRingCat.of (Localization.Away x)
  let g : D.obj j ⟶ B := CommRingCat.ofHom (algebraMap (D.obj j) (Localization.Away x))
  have hg : Et g := by
    change (algebraMap (D.obj j) (Localization.Away x)).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  have hu : IsUnit (φ j x) := isUnit_iff_ne_zero.mpr hx
  let φB : B →+* Ω := IsLocalization.Away.lift x hu
  obtain ⟨k, a, h, hh⟩ := hst j B g hg φB (IsLocalization.Away.lift_comp x hu)
  refine ⟨k, a, ?_⟩
  have e : (D.map a).hom x = h.hom (algebraMap (D.obj j) (Localization.Away x) x) := by
    rw [← hh]; rfl
  rw [e]
  exact (IsLocalization.Away.algebraMap_isUnit x).map h.hom

theorem etaleAbsorbing_of_strongFilteredEtaleSystemExists (h2 : Sys2) : LateralTheory.E.ColimPf.Absorb := Absorb_of (Sys_of h2)

end LateralTheory.E.AbsorbPf
