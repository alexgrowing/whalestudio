import Mathlib
import GroundTheory.GlobalFields.CyclotomicCharacters.Character
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap

namespace GroundTheory.Global

open NumberField IntermediateField

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

abbrev FiniteSubfield : Type := {F : IntermediateField ℚ ℚ̄ // FiniteDimensional ℚ F}

namespace FiniteSubfield

instance (F : FiniteSubfield) : FiniteDimensional ℚ F.1 := F.2

instance (F : FiniteSubfield) : NumberField F.1 where
  to_finiteDimensional := by convert F.2

instance : IsDirectedOrder FiniteSubfield where
  directed F E := ⟨⟨F.1 ⊔ E.1, inferInstance⟩, le_sup_left (a := F.1), le_sup_right (a := F.1)⟩

instance : Nonempty FiniteSubfield := ⟨⟨⊥, inferInstance⟩⟩

abbrev algebraOfLE {F E : FiniteSubfield} (h : F ≤ E) : Algebra F.1 E.1 :=
  (IntermediateField.inclusion (show F.1 ≤ E.1 from h)).toRingHom.toAlgebra

theorem algebraOfLE_algebraMap {F E : FiniteSubfield} (h : F ≤ E) (x : F.1) :
    ((@algebraMap F.1 E.1 _ _ (algebraOfLE h) x : E.1) : ℚ̄) = x :=
  rfl

def ideleClassMap {F E : FiniteSubfield} (h : F ≤ E) :
    IdeleClassGroup F.1 →* IdeleClassGroup E.1 :=
  letI := algebraOfLE h
  GroundTheory.Global.ideleClassMap F.1 E.1

theorem ideleClassMap_mk {F E : FiniteSubfield} (h : F ≤ E) (x : IdeleGroup F.1) :
    ideleClassMap h (IdeleClassGroup.mk F.1 x) =
      IdeleClassGroup.mk E.1 (@ideleEmbedding F.1 E.1 _ _ _ _ (algebraOfLE h) x) :=
  rfl

theorem ideleClassMap_injective {F E : FiniteSubfield} (h : F ≤ E) :
    Function.Injective (ideleClassMap h) :=
  letI := algebraOfLE h
  GroundTheory.Global.ideleClassMap_injective

theorem ideleClassMap_ideleClassMap {F E M : FiniteSubfield} (hFE : F ≤ E) (hEM : E ≤ M)
    (c : IdeleClassGroup F.1) :
    ideleClassMap hEM (ideleClassMap hFE c) = ideleClassMap (hFE.trans hEM) c := by
  let := algebraOfLE hFE
  let := algebraOfLE hEM
  let := algebraOfLE (hFE.trans hEM)
  have : IsScalarTower F.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact GroundTheory.Global.ideleClassMap_ideleClassMap c

@[simp]
theorem ideleClassMap_self {F : FiniteSubfield} (h : F ≤ F) (c : IdeleClassGroup F.1) :
    ideleClassMap h c = c :=
  ideleClassMap_injective h (ideleClassMap_ideleClassMap h h c)

instance directedSystem : DirectedSystem (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ ideleClassMap h) where
  map_self _ c := ideleClassMap_self _ c
  map_map _ _ _ hFE hEM c := ideleClassMap_ideleClassMap hFE hEM c

end FiniteSubfield

def IdeleClassLimit : Type :=
  DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)

namespace IdeleClassLimit

instance : CommGroup IdeleClassLimit :=
  inferInstanceAs (CommGroup (DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)))

def of (F : FiniteSubfield) : IdeleClassGroup F.1 →* IdeleClassLimit where
  toFun c := (⟦⟨F, c⟩⟧ : DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h))
  map_one' := (DirectLimit.one_def (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F).symm
  map_mul' x y := (DirectLimit.mul_def (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F x y).symm

@[simp]
theorem of_ideleClassMap {F E : FiniteSubfield} (h : F ≤ E) (c : IdeleClassGroup F.1) :
    of E (FiniteSubfield.ideleClassMap h c) = of F c :=
  show (⟦⟨E, FiniteSubfield.ideleClassMap h c⟩⟧ : DirectLimit
    (fun F : FiniteSubfield ↦ IdeleClassGroup F.1) (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)) =
      ⟦⟨F, c⟩⟧ from DirectLimit.mk_apply (F := fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
        (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F E c h

theorem of_injective (F : FiniteSubfield) : Function.Injective (of F) :=
  DirectLimit.mk_injective (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap_injective h) F

theorem exists_of (z : IdeleClassLimit) : ∃ (F : FiniteSubfield) (c : IdeleClassGroup F.1),
    of F c = z := by
  obtain ⟨F, c, rfl⟩ := DirectLimit.exists_eq_mk
    (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) z
  exact ⟨F, c, rfl⟩

theorem exists_of₂ (z w : IdeleClassLimit) : ∃ (F : FiniteSubfield) (c d : IdeleClassGroup F.1),
    of F c = z ∧ of F d = w := by
  obtain ⟨F, c, d, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂
    (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) z w
  exact ⟨F, c, d, rfl, rfl⟩

theorem of_eq_of_iff {F E M : FiniteSubfield} (hF : F ≤ M) (hE : E ≤ M) (x : IdeleClassGroup F.1)
    (y : IdeleClassGroup E.1) : of F x = of E y ↔ FiniteSubfield.ideleClassMap hF x = FiniteSubfield.ideleClassMap hE y := by
  rw [← of_ideleClassMap hF x, ← of_ideleClassMap hE y, (of_injective M).eq_iff]

section lift

variable {G : Type*} [CommGroup G] (g : ∀ F : FiniteSubfield, IdeleClassGroup F.1 →* G)
  (compat : ∀ (F E : FiniteSubfield) (h : F ≤ E) (c : IdeleClassGroup F.1),
    g E (FiniteSubfield.ideleClassMap h c) = g F c)

def lift : IdeleClassLimit →* G where
  toFun := DirectLimit.lift (fun _ _ h ↦ FiniteSubfield.ideleClassMap h) (fun F c ↦ g F c)
    fun F E h c ↦ (compat F E h c).symm
  map_one' := by
    obtain ⟨F⟩ := (inferInstance : Nonempty FiniteSubfield)
    have h1 : (1 : IdeleClassLimit) = of F 1 := (map_one _).symm
    rw [h1]
    exact map_one (g F)
  map_mul' z w := by
    obtain ⟨F, c, d, rfl, rfl⟩ := exists_of₂ z w
    rw [← map_mul]
    exact map_mul (g F) c d

@[simp]
theorem lift_of (F : FiniteSubfield) (c : IdeleClassGroup F.1) : lift g compat (of F c) = g F c :=
  rfl

theorem lift_comp_of (F : FiniteSubfield) : (lift g compat).comp (of F) = g F :=
  MonoidHom.ext fun _ ↦ rfl

theorem lift_unique (φ : IdeleClassLimit →* G) (hφ : ∀ F, φ.comp (of F) = g F) :
    φ = lift g compat := by
  ext z
  obtain ⟨F, c, rfl⟩ := exists_of z
  rw [lift_of, ← hφ F, MonoidHom.comp_apply]

end lift

@[ext]
theorem hom_ext {G : Type*} [Monoid G] {φ ψ : IdeleClassLimit →* G}
    (h : ∀ F : FiniteSubfield, φ.comp (of F) = ψ.comp (of F)) : φ = ψ := by
  ext z
  obtain ⟨F, c, rfl⟩ := exists_of z
  exact DFunLike.congr_fun (h F) c

end IdeleClassLimit

end

end GroundTheory.Global
