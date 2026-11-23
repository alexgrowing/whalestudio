import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.SepCech

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

abbrev FinSub : Type := {L : IntermediateField K Ω // FiniteDimensional K L}

instance : IsDirected (FinSub K Ω) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, by haveI := a.2; haveI := b.2; infer_instance⟩, le_sup_left (a := a.1), le_sup_right (b := b.1)⟩⟩

instance : Nonempty (FinSub K Ω) := ⟨⟨⊥, inferInstance⟩⟩

example : IsCofiltered (FinSub K Ω)ᵒᵖ := inferInstance

def ringDiag : FinSub K Ω ⥤ CommRingCat.{0} where
  obj L := CommRingCat.of L.1
  map h := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom h)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

def ringCocone : Cocone (ringDiag K Ω) where
  pt := CommRingCat.of Ω
  ι := { app := fun L => CommRingCat.ofHom L.1.val.toRingHom, naturality := fun _ _ _ => rfl }

abbrev yArr (A : Type) [CommRing A] [Algebra K A] : Arrow PSh :=
  Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap K A))))

theorem ym {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) :
    yoneda.map (Spec.map g) ≫ yoneda.map (Spec.map f) = yoneda.map (Spec.map (f ≫ g)) := by
  rw [← Functor.map_comp, Spec.map_comp]

theorem spec_comm {L L' : FinSub K Ω} (h : L ⟶ L') :
    yoneda.map (Spec.map ((ringDiag K Ω).map h)) ≫ (yArr K L.1).hom = (yArr K L'.1).hom ≫ 𝟙 _ := by
  change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ 𝟙 _
  rw [Category.comp_id]
  refine (ym _ _).trans ?_
  congr 2 <;> (ext; rfl)

def arr : (FinSub K Ω)ᵒᵖ ⥤ Arrow PSh where
  obj L := yArr K L.unop.1
  map h := Arrow.homMk (yoneda.map (Spec.map ((ringDiag K Ω).map h.unop))) (𝟙 _) (spec_comm K Ω h.unop)
  map_id L := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · change yoneda.map (Spec.map (𝟙 _)) = 𝟙 _
      rw [Spec.map_id, yoneda.map_id]
    · rfl
  map_comp f g := by
    refine Arrow.hom_ext _ _ ?_ ?_
    · change yoneda.map (Spec.map ((ringDiag K Ω).map (g.unop ≫ f.unop))) = _
      rw [Functor.map_comp]
      exact (ym _ _).symm
    · exact (Category.comp_id _).symm

def arrCone : Cone (arr K Ω) where
  pt := yArr K Ω
  π := { app := fun L => Arrow.homMk (yoneda.map (Spec.map ((ringCocone K Ω).ι.app L.unop))) (𝟙 _) (by
            change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ 𝟙 _
            rw [Category.comp_id]
            refine (ym _ _).trans ?_
            congr 2 <;> (ext; rfl))
         naturality := fun L L' h => by
            refine Arrow.hom_ext _ _ ?_ ?_
            · change 𝟙 _ ≫ yoneda.map (Spec.map _) = yoneda.map (Spec.map _) ≫ yoneda.map (Spec.map _)
              rw [Category.id_comp]
              refine Eq.trans ?_ (ym _ _).symm
              exact congrArg (fun x => yoneda.map (Spec.map x)) ((ringCocone K Ω).w h.unop).symm
            · exact (Category.comp_id _).symm }

def cechCone : Cone (arr K Ω ⋙ SimplicialObject.cechNerve) := SimplicialObject.cechNerve.mapCone (arrCone K Ω)

example : (cechCone K Ω).pt = cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) := rfl
example (L : (FinSub K Ω)ᵒᵖ) : (arr K Ω ⋙ SimplicialObject.cechNerve).obj L = cech (Spec.map (CommRingCat.ofHom (algebraMap K L.unop.1))) := rfl

end GlobalTheory.SepCech
end
