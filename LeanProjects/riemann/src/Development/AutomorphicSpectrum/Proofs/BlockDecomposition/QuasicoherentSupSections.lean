import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.SupSecs

variable {X : Scheme.{0}} {E : X.Modules}

def sumMap (S T : Subobject E) : (S : X.Modules) ⊞ (T : X.Modules) ⟶ E :=
  biprod.desc S.arrow T.arrow

theorem sup_eq_imageSubobject (S T : Subobject E) : S ⊔ T = imageSubobject (sumMap S T) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · exact Subobject.le_of_comm (biprod.inl ≫ factorThruImageSubobject (sumMap S T))
        (by rw [Category.assoc, imageSubobject_arrow_comp, sumMap, biprod.inl_desc])
    · exact Subobject.le_of_comm (biprod.inr ≫ factorThruImageSubobject (sumMap S T))
        (by rw [Category.assoc, imageSubobject_arrow_comp, sumMap, biprod.inr_desc])
  · refine imageSubobject_le (sumMap S T)
      (biprod.desc (Subobject.ofLE S (S ⊔ T) le_sup_left)
        (Subobject.ofLE T (S ⊔ T) le_sup_right)) ?_
    apply biprod.hom_ext' <;> simp [sumMap]

theorem sumMap_app (S T : Subobject E) (V : X.Opens)
    (x : Γ((S : X.Modules) ⊞ (T : X.Modules), V)) :
    (sumMap S T).app V x =
      S.arrow.app V ((biprod.fst : (S : X.Modules) ⊞ (T : X.Modules) ⟶ _).app V x) +
        T.arrow.app V ((biprod.snd : (S : X.Modules) ⊞ (T : X.Modules) ⟶ _).app V x) := by
  have h : sumMap S T = biprod.fst ≫ S.arrow + biprod.snd ≫ T.arrow := by
    apply biprod.hom_ext' <;> simp [sumMap, Preadditive.comp_add]
  rw [h]
  rfl

theorem sumMap_app_add (S T : Subobject E) (V : X.Opens) (s : Γ((S : X.Modules), V))
    (t : Γ((T : X.Modules), V)) :
    (sumMap S T).app V
        ((biprod.inl : _ ⟶ (S : X.Modules) ⊞ (T : X.Modules)).app V s +
          (biprod.inr : _ ⟶ (S : X.Modules) ⊞ (T : X.Modules)).app V t) =
      S.arrow.app V s + T.arrow.app V t := by
  have hs : biprod.inl ≫ sumMap S T = S.arrow := by simp [sumMap]
  have ht : biprod.inr ≫ sumMap S T = T.arrow := by simp [sumMap]
  rw [map_add, GlobalTheory.QCoh.app_app, GlobalTheory.QCoh.app_app, hs, ht]

end GlobalTheory.CompanionTheory.GE.SupSecs

namespace GlobalTheory.CompanionTheory.GE

open SupSecs in

theorem supsecs {X : Scheme.{0}} {E : X.Modules} (hE : E.IsQuasicoherent) (S T : Subobject E)
    (hS : (S : X.Modules).IsQuasicoherent) (hT : (T : X.Modules).IsQuasicoherent) :
    ((S ⊔ T : Subobject E) : X.Modules).IsQuasicoherent ∧
      ∀ V : X.Opens, IsAffineOpen V →
        secs (S ⊔ T) V = {x | ∃ s ∈ secs S V, ∃ t ∈ secs T V, x = s + t} := by
  rw [sup_eq_imageSubobject]
  refine ⟨GlobalTheory.QCoh.isQuasicoherent_of_iso (imageSubobjectIso (sumMap S T)).symm, fun V hV ↦ ?_⟩
  have hr : secs (imageSubobject (sumMap S T)) V = Set.range ((sumMap S T).app V) := by
    have harrow : (imageSubobject (sumMap S T)).arrow =
        (imageSubobjectIso (sumMap S T)).hom ≫ image.ι (sumMap S T) :=
      (imageSubobject_arrow (sumMap S T)).symm
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := GlobalTheory.QCoh.surjective_factorThruImage_app (sumMap S T) hV
        ((imageSubobjectIso (sumMap S T)).hom.app V a)
      refine ⟨b, ?_⟩
      rw [harrow, ← GlobalTheory.QCoh.app_app, ← hb, GlobalTheory.QCoh.app_app, image.fac]
    · rintro ⟨b, rfl⟩
      refine ⟨(factorThruImageSubobject (sumMap S T)).app V b, ?_⟩
      rw [GlobalTheory.QCoh.app_app, imageSubobject_arrow_comp]
  rw [hr]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, sumMap_app S T V y⟩
  · rintro ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, sumMap_app_add S T V s t⟩

end GlobalTheory.CompanionTheory.GE
