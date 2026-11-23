import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicConverse

open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L₁ L₂ : PeriodPair}

variable (L₁ L₂) in

def latticeHomEquiv : latticeHom L₁ L₂ ≃+ isogHom (weierstrassCurve L₁) (weierstrassCurve L₂) where
  toFun := latticeToHom
  invFun Q := ⟨_, homConst_mem_latticeHom Q⟩
  left_inv α := Subtype.ext (homConst_latticeToHom α)
  right_inv Q := latticeToHom_homConst Q
  map_add' := latticeToHom_add

theorem homPt_latticeHomEquiv (α : latticeHom L₁ L₂) (z : ℂ) :
    homPt (latticeHomEquiv L₁ L₂ α) (toPoint L₁ z) = toPoint L₂ (α * z) :=
  homPt_latticeToHom α z

def torusHom (α : latticeHom L₁ L₂) : Torus L₁ →+ Torus L₂ :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft (α : ℂ)) fun l hl ↦ α.2 l hl

variable (L : PeriodPair)

def latticeEnd : Subring ℂ where
  carrier := {α | ∀ l ∈ L.lattice, α * l ∈ L.lattice}
  add_mem' ha hb := (latticeHom L L).add_mem ha hb
  zero_mem' := (latticeHom L L).zero_mem
  neg_mem' ha := (latticeHom L L).neg_mem ha
  one_mem' l hl := by rwa [one_mul]
  mul_mem' {a b} ha hb l hl := by
    rw [mul_assoc]
    exact ha _ (hb l hl)

def latticeEndEquiv : latticeEnd L ≃+* isogEnd (weierstrassCurve L) where
  toFun α := latticeToHom ⟨α, α.2⟩
  invFun Q := ⟨homConst (weierstrassCurve L) (weierstrassCurve L) Q, homConst_mem_latticeHom Q⟩
  left_inv _ := Subtype.ext (homConst_latticeToHom _)
  right_inv Q := latticeToHom_homConst Q
  map_mul' α β := latticeToHom_mul ⟨α, α.2⟩ ⟨β, β.2⟩ (α * β).2
  map_add' α β := latticeToHom_add ⟨α, α.2⟩ ⟨β, β.2⟩

theorem homConst_latticeEndEquiv (α : latticeEnd L) :
    homConst (weierstrassCurve L) (weierstrassCurve L) (latticeEndEquiv L α) = α :=
  homConst_latticeToHom _

variable {L}

def mulLattice (α : latticeHom L₁ L₂) : AddSubgroup L₂.lattice where
  carrier := {w | ∃ l ∈ L₁.lattice, (w : ℂ) = α * l}
  add_mem' := by
    rintro a b ⟨l, hl, ha⟩ ⟨l', hl', hb⟩
    exact ⟨l + l', add_mem hl hl', by rw [Submodule.coe_add, ha, hb, mul_add]⟩
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    rintro a ⟨l, hl, ha⟩
    exact ⟨-l, neg_mem hl, by rw [Submodule.coe_neg, ha, mul_neg]⟩

theorem mem_mulLattice {α : latticeHom L₁ L₂} {w : L₂.lattice} :
    w ∈ mulLattice α ↔ ∃ l ∈ L₁.lattice, (w : ℂ) = α * l :=
  Iff.rfl

def kerMap (α : latticeHom L₁ L₂) (h0 : (α : ℂ) ≠ 0) :
    L₂.lattice →+ (homPt (latticeHomEquiv L₁ L₂ α)).ker where
  toFun w := ⟨toPoint L₁ (w / α), by
    rw [AddMonoidHom.mem_ker, homPt_latticeHomEquiv, mul_div_cancel₀ _ h0]
    exact toPoint_of_mem w.2⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Subtype.ext
    simp only [Submodule.coe_add, add_div, AddMemClass.mk_add_mk, toPoint_add]

theorem kerMap_surjective (α : latticeHom L₁ L₂) (h0 : (α : ℂ) ≠ 0) :
    Function.Surjective (kerMap α h0) := by
  rintro ⟨P, hP⟩
  obtain ⟨z, rfl⟩ := toPoint_surjective (L := L₁) P
  rw [AddMonoidHom.mem_ker, homPt_latticeHomEquiv, toPoint_eq_zero_iff] at hP
  refine ⟨⟨_, hP⟩, Subtype.ext ?_⟩
  show toPoint L₁ (α * z / α) = toPoint L₁ z
  rw [mul_div_cancel_left₀ _ h0]

theorem ker_kerMap (α : latticeHom L₁ L₂) (h0 : (α : ℂ) ≠ 0) :
    (kerMap α h0).ker = mulLattice α := by
  ext w
  rw [AddMonoidHom.mem_ker, mem_mulLattice]
  constructor
  · intro h
    have h' : toPoint L₁ (w / α) = 0 := congrArg Subtype.val h
    rw [toPoint_eq_zero_iff] at h'
    exact ⟨_, h', by rw [mul_div_cancel₀ _ h0]⟩
  · rintro ⟨l, hl, hw⟩
    apply Subtype.ext
    show toPoint L₁ (w / α) = 0
    rw [hw, mul_div_cancel_left₀ _ h0]
    exact toPoint_of_mem hl

def kerEquiv (α : latticeHom L₁ L₂) (h0 : (α : ℂ) ≠ 0) :
    (homPt (latticeHomEquiv L₁ L₂ α)).ker ≃+ L₂.lattice ⧸ mulLattice α :=
  ((QuotientAddGroup.quotientAddEquivOfEq (ker_kerMap α h0)).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (kerMap_surjective α h0))).symm

end Elliptic
end GroundTheory.Global
