import Mathlib
import GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassEquivIdeleClassMapOfComm
import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleLimit

open FiniteSubfield

def ideleMap {F E : FiniteSubfield} (h : F ≤ E) : IdeleGroup F.1 →* IdeleGroup E.1 :=
  letI := algebraOfLE h
  ideleEmbedding F.1 E.1

theorem ideleMap_injective {F E : FiniteSubfield} (h : F ≤ E) : Function.Injective (ideleMap h) :=
  letI := algebraOfLE h
  ideleEmbedding_injective

theorem ideleMap_ideleMap {F E M : FiniteSubfield} (hFE : F ≤ E) (hEM : E ≤ M) (x : IdeleGroup F.1) :
    ideleMap hEM (ideleMap hFE x) = ideleMap (hFE.trans hEM) x := by
  let := algebraOfLE hFE
  let := algebraOfLE hEM
  let := algebraOfLE (hFE.trans hEM)
  have : IsScalarTower F.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact ideleEmbedding_ideleEmbedding x

@[simp]
theorem ideleMap_self {F : FiniteSubfield} (h : F ≤ F) (x : IdeleGroup F.1) : ideleMap h x = x :=
  ideleMap_injective h (ideleMap_ideleMap h h x)

theorem ideleClassMap_mk {F E : FiniteSubfield} (h : F ≤ E) (x : IdeleGroup F.1) :
    FiniteSubfield.ideleClassMap h (IdeleClassGroup.mk F.1 x) =
      IdeleClassGroup.mk E.1 (ideleMap h x) :=
  rfl

instance directedSystem : DirectedSystem (fun F : FiniteSubfield ↦ IdeleGroup F.1)
    (fun _ _ h ↦ ideleMap h) where
  map_self _ x := ideleMap_self _ x
  map_map _ _ _ hFE hEM x := ideleMap_ideleMap hFE hEM x

end IdeleLimit

def IdeleLimit : Type :=
  DirectLimit (fun F : FiniteSubfield ↦ IdeleGroup F.1) (fun _ _ h ↦ IdeleLimit.ideleMap h)

namespace IdeleLimit

open FiniteSubfield

instance : CommGroup IdeleLimit :=
  inferInstanceAs (CommGroup (DirectLimit (fun F : FiniteSubfield ↦ IdeleGroup F.1)
    (fun _ _ h ↦ ideleMap h)))

set_option maxHeartbeats 1000000 in

def of (F : FiniteSubfield) : IdeleGroup F.1 →* IdeleLimit where
  toFun x := (⟦⟨F, x⟩⟧ : DirectLimit (fun F : FiniteSubfield ↦ IdeleGroup F.1)
    (fun _ _ h ↦ ideleMap h))
  map_one' := (DirectLimit.one_def (f := fun _ _ h ↦ ideleMap h) F).symm
  map_mul' x y := (DirectLimit.mul_def (f := fun _ _ h ↦ ideleMap h) F x y).symm

@[simp]
theorem of_ideleMap {F E : FiniteSubfield} (h : F ≤ E) (x : IdeleGroup F.1) :
    of E (ideleMap h x) = of F x :=
  show (⟦⟨E, ideleMap h x⟩⟧ : DirectLimit
    (fun F : FiniteSubfield ↦ IdeleGroup F.1) (fun _ _ h ↦ ideleMap h)) =
      ⟦⟨F, x⟩⟧ from DirectLimit.mk_apply (F := fun F : FiniteSubfield ↦ IdeleGroup F.1)
        (f := fun _ _ h ↦ ideleMap h) F E x h

theorem of_injective (F : FiniteSubfield) : Function.Injective (of F) :=
  DirectLimit.mk_injective (f := fun _ _ h ↦ ideleMap h) (fun _ _ h ↦ ideleMap_injective h) F

theorem exists_of (z : IdeleLimit) : ∃ (F : FiniteSubfield) (x : IdeleGroup F.1), of F x = z := by
  obtain ⟨F, x, rfl⟩ := DirectLimit.exists_eq_mk (f := fun _ _ h ↦ ideleMap h) z
  exact ⟨F, x, rfl⟩

theorem exists_of₂ (z w : IdeleLimit) : ∃ (F : FiniteSubfield) (x y : IdeleGroup F.1),
    of F x = z ∧ of F y = w := by
  obtain ⟨F, x, y, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (f := fun _ _ h ↦ ideleMap h) z w
  exact ⟨F, x, y, rfl, rfl⟩

theorem of_eq_of_iff {F E M : FiniteSubfield} (hF : F ≤ M) (hE : E ≤ M) (x : IdeleGroup F.1)
    (y : IdeleGroup E.1) : of F x = of E y ↔ ideleMap hF x = ideleMap hE y := by
  rw [← of_ideleMap hF x, ← of_ideleMap hE y, (of_injective M).eq_iff]

section lift

variable {A : Type*} [CommGroup A] (g : ∀ F : FiniteSubfield, IdeleGroup F.1 →* A)
  (compat : ∀ (F E : FiniteSubfield) (h : F ≤ E) (x : IdeleGroup F.1), g E (ideleMap h x) = g F x)

def lift : IdeleLimit →* A where
  toFun := DirectLimit.lift (fun _ _ h ↦ ideleMap h) (fun F x ↦ g F x)
    fun F E h x ↦ (compat F E h x).symm
  map_one' := by
    obtain ⟨F⟩ := (inferInstance : Nonempty FiniteSubfield)
    have h1 : (1 : IdeleLimit) = of F 1 := (map_one _).symm
    rw [h1]
    exact map_one (g F)
  map_mul' z w := by
    obtain ⟨F, x, y, rfl, rfl⟩ := exists_of₂ z w
    rw [← map_mul]
    exact map_mul (g F) x y

@[simp]
theorem lift_of (F : FiniteSubfield) (x : IdeleGroup F.1) : lift g compat (of F x) = g F x :=
  rfl

end lift

@[ext]
theorem hom_ext {A : Type*} [Monoid A] {φ ψ : IdeleLimit →* A}
    (h : ∀ F : FiniteSubfield, φ.comp (of F) = ψ.comp (of F)) : φ = ψ := by
  ext z
  obtain ⟨F, x, rfl⟩ := exists_of z
  exact DFunLike.congr_fun (h F) x

theorem of_ideleEquiv_congr {F E E' : FiniteSubfield} (τ : F.1 ≃+* E.1) (τ' : F.1 ≃+* E'.1)
    (h : ∀ x : F.1, (τ x : ℚ̄) = τ' x) (x : IdeleGroup F.1) :
    of E (ideleEquiv τ x) = of E' (ideleEquiv τ' x) := by
  have hE : E = E' := by
    refine Subtype.ext (SetLike.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩)
    · obtain ⟨z, hz⟩ := τ.surjective ⟨y, hy⟩
      have hy' : y = ((τ' z : E'.1) : ℚ̄) := by rw [← h z, hz]
      rw [hy']
      exact (τ' z).2
    · obtain ⟨z, hz⟩ := τ'.surjective ⟨y, hy⟩
      have hy' : y = ((τ z : E.1) : ℚ̄) := by rw [h z, hz]
      rw [hy']
      exact (τ z).2
  subst hE
  have : τ = τ' := RingEquiv.ext fun z ↦ Subtype.ext (h z)
  rw [this]

def conjOf (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) : IdeleGroup F.1 →* IdeleLimit :=
  (of (map σ F)).comp (ideleEquiv (mapEquiv σ F)).toMulEquiv.toMonoidHom

theorem conjOf_compat (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F E : FiniteSubfield) (h : F ≤ E) (x : IdeleGroup F.1) :
    conjOf σ E (ideleMap h x) = conjOf σ F x := by
  change of (map σ E) (ideleEquiv (mapEquiv σ E) (ideleMap h x)) =
    of (map σ F) (ideleEquiv (mapEquiv σ F) x)
  rw [ideleMap]
  let := algebraOfLE h
  let := algebraOfLE (map_mono σ h)
  rw [ideleEquiv_ideleEmbedding_of_comm (mapEquiv σ F) (mapEquiv σ E) (fun x ↦ rfl)]
  exact of_ideleMap (map_mono σ h) _

def galoisHom (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) : IdeleLimit →* IdeleLimit :=
  lift (conjOf σ) (conjOf_compat σ)

theorem galoisHom_of (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (x : IdeleGroup F.1) :
    galoisHom σ (of F x) = of (map σ F) (ideleEquiv (mapEquiv σ F) x) :=
  rfl

theorem galoisHom_one (z : IdeleLimit) : galoisHom 1 z = z := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  rw [galoisHom_of]
  refine (of_ideleEquiv_congr (mapEquiv 1 F) (RingEquiv.refl F.1) (fun x ↦ rfl) x).trans ?_
  rw [ideleEquiv_refl]

theorem galoisHom_mul (σ τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (z : IdeleLimit) :
    galoisHom (σ * τ) z = galoisHom σ (galoisHom τ z) := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  rw [galoisHom_of, galoisHom_of, galoisHom_of, ← ideleEquiv_trans]
  exact of_ideleEquiv_congr (mapEquiv (σ * τ) F)
    ((mapEquiv τ F).trans (mapEquiv σ (map τ F))) (fun x ↦ rfl) x

instance : MulDistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleLimit where
  smul σ z := galoisHom σ z
  one_smul := galoisHom_one
  mul_smul := galoisHom_mul
  smul_one σ := map_one (galoisHom σ)
  smul_mul σ := map_mul (galoisHom σ)

theorem smul_def (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (z : IdeleLimit) : σ • z = galoisHom σ z :=
  rfl

theorem smul_of (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (x : IdeleGroup F.1) :
    σ • of F x = of (map σ F) (ideleEquiv (mapEquiv σ F) x) :=
  rfl

theorem smul_of_eq_of_mem_fixingSubgroup {F : FiniteSubfield} {σ : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (hσ : σ ∈ F.1.fixingSubgroup) (x : IdeleGroup F.1) : σ • of F x = of F x := by
  rw [smul_of]
  refine (of_ideleEquiv_congr (mapEquiv σ F) (RingEquiv.refl F.1)
    (fun y ↦ (IntermediateField.mem_fixingSubgroup_iff F.1 σ).1 hσ y y.2) x).trans ?_
  rw [ideleEquiv_refl]

abbrev rep : Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄) := Rep.ofMulDistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleLimit

instance isDiscreteRep : IsDiscreteRep rep := by
  refine (isDiscreteRep_iff rep).2 fun z => ?_
  obtain ⟨F, x, rfl⟩ := exists_of (Additive.toMul z)
  have : FiniteDimensional ℚ F.1 := F.2
  refine Subgroup.isOpen_mono (H₁ := F.1.fixingSubgroup) (fun σ hσ ↦ ?_) F.1.fixingSubgroup_isOpen
  exact congrArg Additive.ofMul (smul_of_eq_of_mem_fixingSubgroup hσ x)

def toClassLimit : IdeleLimit →* IdeleClassLimit :=
  lift (fun F ↦ (IdeleClassLimit.of F).comp (IdeleClassGroup.mk F.1)) fun F E h x ↦ by
    change IdeleClassLimit.of E (IdeleClassGroup.mk E.1 (ideleMap h x)) =
      IdeleClassLimit.of F (IdeleClassGroup.mk F.1 x)
    rw [← ideleClassMap_mk, IdeleClassLimit.of_ideleClassMap]

@[simp]
theorem toClassLimit_of (F : FiniteSubfield) (x : IdeleGroup F.1) :
    toClassLimit (of F x) = IdeleClassLimit.of F (IdeleClassGroup.mk F.1 x) :=
  rfl

theorem toClassLimit_smul (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (z : IdeleLimit) :
    toClassLimit (σ • z) = σ • toClassLimit z := by
  obtain ⟨F, x, rfl⟩ := exists_of z
  rw [smul_of, toClassLimit_of, toClassLimit_of, IdeleClassLimit.smul_of, ideleClassEquiv_mk]

theorem toClassLimit_surjective : Function.Surjective toClassLimit := by
  intro c
  obtain ⟨F, c, rfl⟩ := IdeleClassLimit.exists_of c
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective F.1 c
  exact ⟨of F x, rfl⟩

end IdeleLimit

end

end GroundTheory.ProfCoh
