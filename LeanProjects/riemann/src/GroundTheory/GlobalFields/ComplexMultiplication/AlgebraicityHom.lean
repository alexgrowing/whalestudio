import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.Endomorphisms

open WeierstrassCurve GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point)

noncomputable section

namespace GroundTheory.Global

universe u

section FFMap

variable {F F' : Type u} [Field F] [Field F'] (σ : F →+* F')

theorem ffMap_surjective (hσ : Function.Surjective σ) (E : WeierstrassCurve F) :
    Function.Surjective (ffMap σ E) := by
  let R : IntermediateField F' (E.map σ).toAffine.FunctionField :=
    { (ffMap σ E).fieldRange with
      algebraMap_mem' := fun c => by
        obtain ⟨a, rfl⟩ := hσ c
        exact ⟨algebraMap F _ a, ffMap_algebraMap σ E a⟩ }
  have hR : R = ⊤ := by
    rw [eq_top_iff, ← adjoin_genX_genY (W := E.map σ), IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact ⟨genX E, ffMap_genX σ E⟩
    · exact ⟨genY E, ffMap_genY σ E⟩
  intro z
  have hz : z ∈ R := hR ▸ IntermediateField.mem_top
  exact hz

end FFMap

section BcPt

variable {F F' : Type u} [Field F] [Field F'] [Algebra F F'] (E E' : WeierstrassCurve F)

def bcPtMap : (E'.baseChange E.toAffine.FunctionField).toAffine.Point →+
    ((E'.baseChange F').baseChange (E.baseChange F').toAffine.FunctionField).toAffine.Point :=
  Point.map (W' := E') (bcEmb (F' := F') E)

end BcPt

section HomMap

variable {F F' : Type u} [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F]
  [DecidableEq F'] (σ : F →+* F') {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]
  [E''.IsElliptic]

def homPtMap : (E'.baseChange E.toAffine.FunctionField).toAffine.Point →+
    ((E'.map σ).baseChange (E.map σ).toAffine.FunctionField).toAffine.Point :=
  letI := σ.toAlgebra
  bcPtMap (F' := F') E E'

omit [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F] [DecidableEq F'] in
theorem homPtMap_isogeny (φ : Isogeny E E') : homPtMap σ φ.1 = (φ.map σ).1 := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  exact (isogBaseChange_val (F' := F') φ).symm

omit [IsAlgClosed F'] [DecidableEq F'] in
theorem homPtMap_mem (Q : isogHom E E') : homPtMap σ Q.1 ∈ isogHom (E.map σ) (E'.map σ) := by
  by_cases hQ : Q = 0
  · rw [hQ, ZeroMemClass.coe_zero, map_zero]
    exact zero_mem _
  · rw [← isogOfHom_val Q hQ, homPtMap_isogeny]
    exact ((isogOfHom Q hQ).map σ).toHom.2

def homMap : isogHom E E' →+ isogHom (E.map σ) (E'.map σ) where
  toFun Q := ⟨homPtMap σ Q.1, homPtMap_mem σ Q⟩
  map_zero' := Subtype.ext (map_zero (homPtMap σ))
  map_add' Q₁ Q₂ := Subtype.ext (map_add (homPtMap σ) Q₁.1 Q₂.1)

theorem homMap_toHom (φ : Isogeny E E') : homMap σ φ.toHom = (φ.map σ).toHom :=
  Subtype.ext rfl

theorem homConst_toHom (φ : Isogeny E E') : homConst E E' φ.toHom = invConst φ := by
  apply (algebraMap F E.toAffine.FunctionField).injective
  rw [algebraMap_homConst, algebraMap_invConst]
  rfl

omit [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F] [DecidableEq F'] in

theorem invConst_map (φ : Isogeny E E') : invConst (φ.map σ) = σ (invConst φ) := by
  let _ := σ.toAlgebra
  let _ := Classical.decEq F'
  exact invConst_isogBaseChange (F' := F') φ

theorem homConst_homMap (Q : isogHom E E') :
    homConst (E.map σ) (E'.map σ) (homMap σ Q) = σ (homConst E E' Q) := by
  by_cases hQ : Q = 0
  · rw [hQ, map_zero, map_zero, map_zero, map_zero]
  · rw [← isogOfHom_toHom Q hQ, homMap_toHom, homConst_toHom, homConst_toHom, invConst_map]

theorem homMap_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homMap σ (homComp R Q) = homComp (homMap σ R) (homMap σ Q) := by
  by_cases hQ : Q = 0
  · simp only [hQ, homComp_zero_right, map_zero]
  by_cases hR : R = 0
  · simp only [hR, homComp_zero_left, map_zero]
  rw [← isogOfHom_toHom Q hQ, ← isogOfHom_toHom R hR, Isogeny.homComp_toHom, homMap_toHom,
    homMap_toHom, homMap_toHom, Isogeny.homComp_toHom, Isogeny.map_comp]

theorem homMap_one : homMap σ (1 : isogEnd E) = 1 := by
  rw [isogEnd_one_eq_mulIsogeny, homMap_toHom, Isogeny.map_mulIsogeny, ← isogEnd_one_eq_mulIsogeny]

def endMap : isogEnd E →+* isogEnd (E.map σ) where
  toFun := homMap σ
  map_one' := homMap_one σ
  map_mul' f g := homMap_homComp σ f g
  map_zero' := map_zero _
  map_add' := map_add _

theorem homMap_injective : Function.Injective (homMap σ : isogHom E E' → _) := by
  rw [injective_iff_map_eq_zero]
  intro Q hQ
  by_contra h
  rw [← isogOfHom_toHom Q h, homMap_toHom] at hQ
  exact Isogeny.toHom_ne_zero _ hQ

theorem homMap_surjective (hσ : Function.Surjective σ) :
    Function.Surjective (homMap σ : isogHom E E' → _) := by
  intro P
  by_cases hP : P = 0
  · exact ⟨0, by rw [hP, map_zero]⟩
  set ψ := isogOfHom P hP
  obtain ⟨x, hx⟩ := ffMap_surjective σ hσ E ψ.x
  obtain ⟨y, hy⟩ := ffMap_surjective σ hσ E ψ.y
  refine ⟨(Isogeny.ofMap σ ψ x y hx hy).toHom, ?_⟩
  rw [homMap_toHom, Isogeny.map_ofMap, isogOfHom_toHom]

def endMapEquiv (σ : F ≃+* F') : isogEnd E ≃+* isogEnd (E.map (σ : F →+* F')) :=
  RingEquiv.ofBijective (endMap (σ : F →+* F'))
    ⟨homMap_injective (σ : F →+* F'), homMap_surjective (σ : F →+* F') σ.surjective⟩

end HomMap

section ConstSet

open Elliptic

variable {F F' : Type u} [Field F] [Field F'] [IsAlgClosed F] [IsAlgClosed F'] [DecidableEq F]
  [DecidableEq F']

variable (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic] in

def homConstSet : AddSubgroup F := (homConst E E').range

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem mem_homConstSet {c : F} :
    c ∈ homConstSet E E' ↔ ∃ Q : isogHom E E', homConst E E' Q = c :=
  AddMonoidHom.mem_range

theorem homConstSet_map (σ : F ≃+* F') :
    (homConstSet (E.map (σ : F →+* F')) (E'.map (σ : F →+* F')) : Set F') =
      σ '' homConstSet E E' := by
  ext z
  simp only [SetLike.mem_coe, mem_homConstSet, Set.mem_image]
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨Q, rfl⟩ := homMap_surjective (E := E) (E' := E') (σ : F →+* F') σ.surjective P
    exact ⟨homConst E E' Q, ⟨Q, rfl⟩, (homConst_homMap (σ : F →+* F') Q).symm⟩
  · rintro ⟨c, ⟨Q, rfl⟩, rfl⟩
    exact ⟨homMap (σ : F →+* F') Q, homConst_homMap (σ : F →+* F') Q⟩

theorem homConst_vcHom_mul_inv (C : VariableChange F) (h : C • E = E') :
    homConst E' E (vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)) * homConst E E' (vcHom C h) = 1 := by
  rw [← homConst_homComp, homComp_vcHom_vcHom C C⁻¹ rfl h (inv_smul_eq_of_smul_eq C h), homConst_homId]

theorem homConstSet_le_mul {E₁ E₁' : WeierstrassCurve F} [E₁.IsElliptic] [E₁'.IsElliptic]
    (Q : isogHom E₁ E) (R : isogHom E' E₁') {z : F} (hz : z ∈ homConstSet E E') :
    homConst E' E₁' R * z * homConst E₁ E Q ∈ homConstSet E₁ E₁' := by
  obtain ⟨P, rfl⟩ := mem_homConstSet.1 hz
  exact mem_homConstSet.2
    ⟨homComp R (homComp P Q), by rw [homConst_homComp, homConst_homComp, mul_assoc]⟩

theorem homConstSet_vc {E₁ E₁' : WeierstrassCurve F} [E₁.IsElliptic] [E₁'.IsElliptic]
    (C C' : VariableChange F) (h : C • E = E₁) (h' : C' • E' = E₁') :
    ∃ c : F, c ≠ 0 ∧ (homConstSet E₁ E₁' : Set F) = (c * ·) '' homConstSet E E' := by
  set Q := vcHom C⁻¹ (inv_smul_eq_of_smul_eq C h)
  set R := vcHom C' h'
  set Q' := vcHom C h
  set R' := vcHom C'⁻¹ (inv_smul_eq_of_smul_eq C' h')
  have e1 : homConst E₁ E Q * homConst E E₁ Q' = 1 := homConst_vcHom_mul_inv C h
  have e2 : homConst E₁' E' R' * homConst E' E₁' R = 1 := homConst_vcHom_mul_inv C' h'
  set c := homConst E' E₁' R * homConst E₁ E Q
  have hc : c * (homConst E₁' E' R' * homConst E E₁ Q') = 1 := by
    linear_combination (homConst E₁' E' R' * homConst E' E₁' R) * e1 + e2
  refine ⟨c, left_ne_zero_of_mul_eq_one hc, ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    refine ⟨homConst E₁' E' R' * z * homConst E E₁ Q', homConstSet_le_mul Q' R' hz, ?_⟩
    linear_combination z * hc
  · rintro ⟨w, hw, rfl⟩
    have := homConstSet_le_mul Q R hw
    convert this using 1
    ring

end ConstSet

section Lattice

open Elliptic

theorem homConstSet_weierstrassCurve (L₁ L₂ : PeriodPair) :
    homConstSet (weierstrassCurve L₁) (weierstrassCurve L₂) = latticeHom L₁ L₂ := by
  ext z
  rw [mem_homConstSet]
  constructor
  · rintro ⟨Q, rfl⟩
    exact homConst_mem_latticeHom Q
  · intro hz
    exact ⟨latticeToHom ⟨z, hz⟩, homConst_latticeToHom ⟨z, hz⟩⟩

end Lattice

end GroundTheory.Global
