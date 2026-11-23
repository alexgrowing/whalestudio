import Development.EtaleCohomology.EtaleSheaves.AbsorbPf

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.EWeil.AbsorbPf

def Model : Prop := ∀ (A : CommRingCat.{0}), ∃ (N : Type) (M : N → CommRingCat.{0}) (tM : ∀ n, A ⟶ M n),
  (∀ n, Et (tM n)) ∧ ∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∃ (n : N) (e : B ≅ M n), g ≫ e.hom = tM n

def Pair : Prop := ∀ (A B C : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω) (gB : A ⟶ B) (gC : A ⟶ C),
  Et gB → Et gC → ∀ (φB : B →+* Ω) (φC : C →+* Ω), φB.comp gB.hom = ι → φC.comp gC.hom = ι →
  ∃ (E : CommRingCat.{0}) (gE : A ⟶ E) (φE : E →+* Ω) (p : B ⟶ E) (q : C ⟶ E), Et gE ∧ φE.comp gE.hom = ι ∧
    gB ≫ p = gE ∧ gC ≫ q = gE ∧ φE.comp p.hom = φB ∧ φE.comp q.hom = φC

def Coeq : Prop := ∀ (A B C : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω) (gB : A ⟶ B) (gC : A ⟶ C),
  Et gB → Et gC → ∀ (φB : B →+* Ω) (φC : C →+* Ω), φB.comp gB.hom = ι → φC.comp gC.hom = ι →
  ∀ (u v : B ⟶ C), gB ≫ u = gC → gB ≫ v = gC → φC.comp u.hom = φB → φC.comp v.hom = φB →
  ∃ (E : CommRingCat.{0}) (gE : A ⟶ E) (φE : E →+* Ω) (w : C ⟶ E), Et gE ∧ φE.comp gE.hom = ι ∧
    gC ≫ w = gE ∧ φE.comp w.hom = φC ∧ u ≫ w = v ≫ w

theorem et_comp {A B C : CommRingCat.{0}} {f : A ⟶ B} {g : B ⟶ C} (hf : Et f) (hg : Et g) : Et (f ≫ g) := by
  change (f ≫ g).hom.Etale
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _ hf hg

theorem et_id (A : CommRingCat.{0}) : Et (𝟙 A) := by
  change (𝟙 A : A ⟶ A).hom.Etale
  rw [CommRingCat.hom_id]
  exact (RingHom.etale_algebraMap (R := A) (S := A)).mpr inferInstance

section Cat
variable {A : CommRingCat.{0}} {Ω : Type} [Field Ω] (ι : A →+* Ω) {N : Type} (M : N → CommRingCat.{0})
  (tM : ∀ n, A ⟶ M n)

structure Obj where
  n : N
  φ : M n →+* Ω
  hφ : φ.comp (tM n).hom = ι

variable {ι M tM}

def Hm (X Y : Obj ι M tM) : Type := {h : M X.n ⟶ M Y.n // tM X.n ≫ h = tM Y.n ∧ Y.φ.comp h.hom = X.φ}

instance cat : SmallCategory (Obj ι M tM) where
  Hom X Y := Hm X Y
  id X := ⟨𝟙 _, by simp, by simp⟩
  comp f g := ⟨f.1 ≫ g.1, by rw [← Category.assoc, f.2.1, g.2.1], by
    rw [CommRingCat.hom_comp, ← RingHom.comp_assoc, g.2.2, f.2.2]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f g h := Subtype.ext (Category.assoc _ _ _)

@[simp] theorem comp_val {X Y Z : Obj ι M tM} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (show Hm X Z from f ≫ g).1 = (show Hm X Y from f).1 ≫ (show Hm Y Z from g).1 := rfl
@[simp] theorem id_val (X : Obj ι M tM) : (show Hm X X from 𝟙 X).1 = 𝟙 _ := rfl

def Dfun : Obj ι M tM ⥤ CommRingCat.{0} where
  obj X := M X.n
  map f := (show Hm _ _ from f).1

end Cat

theorem Sys2_of (hM : Model) (hP : Pair) (hC : Coeq) : LateralTheory.E.AbsorbPf.Sys2 := by
  intro A Ω _ ι
  obtain ⟨N, M, tM, hEt, hmod⟩ := hM A

  have into : ∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = ι →
      ∃ (X : Obj ι M tM) (e : B ≅ M X.n), g ≫ e.hom = tM X.n ∧ X.φ.comp e.hom.hom = φB := by
    intro B g hg φB hφB
    obtain ⟨n, e, he⟩ := hmod B g hg
    refine ⟨⟨n, φB.comp e.inv.hom, ?_⟩, e, he, ?_⟩
    · have h1 : (φB.comp e.inv.hom).comp (g ≫ e.hom).hom = φB.comp (g ≫ e.hom ≫ e.inv).hom := by
        simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
      rw [← he, h1, Iso.hom_inv_id, Category.comp_id, hφB]
    · show (φB.comp e.inv.hom).comp e.hom.hom = φB
      rw [RingHom.comp_assoc, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, RingHom.comp_id]
  haveI : IsFilteredOrEmpty (Obj ι M tM) := by
    refine ⟨?_, ?_⟩
    · intro X Y
      obtain ⟨E, gE, φE, p, q, hE, hφE, hp, hq, hpφ, hqφ⟩ :=
        hP A (M X.n) (M Y.n) Ω ι (tM X.n) (tM Y.n) (hEt _) (hEt _) X.φ Y.φ X.hφ Y.hφ
      obtain ⟨Z, e, he, heφ⟩ := into E gE hE φE hφE
      refine ⟨Z, (⟨p ≫ e.hom, ?_, ?_⟩ : Hm X Z), (⟨q ≫ e.hom, ?_, ?_⟩ : Hm Y Z), trivial⟩
      · rw [← Category.assoc, hp, he]
      · rw [CommRingCat.hom_comp, ← RingHom.comp_assoc, heφ, hpφ]
      · rw [← Category.assoc, hq, he]
      · rw [CommRingCat.hom_comp, ← RingHom.comp_assoc, heφ, hqφ]
    · intro X Y f g
      obtain ⟨E, gE, φE, w, hE, hφE, hw, hwφ, huv⟩ :=
        hC A (M X.n) (M Y.n) Ω ι (tM X.n) (tM Y.n) (hEt _) (hEt _) X.φ Y.φ X.hφ Y.hφ
          (show Hm X Y from f).1 (show Hm X Y from g).1 (show Hm X Y from f).2.1 (show Hm X Y from g).2.1
          (show Hm X Y from f).2.2 (show Hm X Y from g).2.2
      obtain ⟨Z, e, he, heφ⟩ := into E gE hE φE hφE
      refine ⟨Z, (⟨w ≫ e.hom, ?_, ?_⟩ : Hm Y Z), ?_⟩
      · rw [← Category.assoc, hw, he]
      · rw [CommRingCat.hom_comp, ← RingHom.comp_assoc, heφ, hwφ]
      · apply Subtype.ext
        show (show Hm X Y from f).1 ≫ (w ≫ e.hom) = (show Hm X Y from g).1 ≫ (w ≫ e.hom)
        rw [← Category.assoc, huv, Category.assoc]
  haveI : Nonempty (Obj ι M tM) := by
    obtain ⟨X, _, _, _⟩ := into A (𝟙 A) (et_id A) ι (by simp)
    exact ⟨X⟩
  haveI : IsFiltered (Obj ι M tM) := {}
  let D : Obj ι M tM ⥤ CommRingCat.{0} := Dfun
  let t : (Functor.const (Obj ι M tM)).obj A ⟶ D :=
    { app := fun X => tM X.n
      naturality := by
        intro X Y f
        simp only [Functor.const_obj_obj, Functor.const_obj_map]
        exact ((show Hm X Y from f).2.1).symm }
  refine ⟨Obj ι M tM, inferInstance, inferInstance, D, t, fun X => X.φ, fun X => hEt X.n, fun X => X.hφ,
    fun X Y f => (show Hm X Y from f).2.2, ?_, ?_⟩
  · intro B g hg φB hφB
    obtain ⟨X, e, he, heφ⟩ := into B g hg φB hφB
    exact ⟨X, e.hom, he, heφ⟩
  · intro X B g hg φB hφB
    let g' : M X.n ⟶ B := g
    have hg' : Et g' := hg
    have hφB' : φB.comp g'.hom = X.φ := hφB
    have hφ' : φB.comp (tM X.n ≫ g').hom = ι := by
      rw [CommRingCat.hom_comp, ← RingHom.comp_assoc, hφB', X.hφ]
    obtain ⟨Y, e, he, heφ⟩ := into B (tM X.n ≫ g') (et_comp (hEt _) hg') φB hφ'
    refine ⟨Y, (⟨g' ≫ e.hom, by rw [← Category.assoc, he], ?_⟩ : Hm X Y), e.hom, rfl⟩
    rw [CommRingCat.hom_comp, ← RingHom.comp_assoc, heφ, hφB']

theorem Absorb_of (hM : Model) (hP : Pair) (hC : Coeq) : LateralTheory.E.ColimPf.Absorb :=
  LateralTheory.E.AbsorbPf.etaleAbsorbing_of_strongFilteredEtaleSystemExists (Sys2_of hM hP hC)

end LateralTheory.EWeil.AbsorbPf
