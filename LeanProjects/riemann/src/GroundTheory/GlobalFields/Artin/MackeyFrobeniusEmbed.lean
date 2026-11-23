import Mathlib
import GroundTheory.GlobalFields.Artin.MackeyFrobenius
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise

namespace GroundTheory.Global.Artin

variable {G : Type*} [Group G] {H D I : Subgroup G}

def dxToQuot (H D I : Subgroup G) [(I.subgroupOf D).Normal] (x : G) :
    (MulAut.conj x • D : Subgroup G).subgroupOf H →* D ⧸ I.subgroupOf D :=
  (QuotientGroup.mk' (I.subgroupOf D)).comp
    { toFun := fun d ↦ ⟨x⁻¹ * ((d : H) : G) * x,
        (mem_conj_smul_iff D x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩
      map_one' := by
        apply Subtype.ext
        change x⁻¹ * (1 : G) * x = 1
        group
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        change x⁻¹ * (((a : H) : G) * ((b : H) : G)) * x =
          (x⁻¹ * ((a : H) : G) * x) * (x⁻¹ * ((b : H) : G) * x)
        group }

theorem dxToQuot_apply [(I.subgroupOf D).Normal] (x : G)
    (d : (MulAut.conj x • D : Subgroup G).subgroupOf H) :
    dxToQuot H D I x d = ((⟨x⁻¹ * ((d : H) : G) * x,
      (mem_conj_smul_iff D x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩ : D) : D ⧸ I.subgroupOf D) :=
  rfl

theorem ker_dxToQuot [(I.subgroupOf D).Normal] (x : G) :
    (dxToQuot H D I x).ker = ((MulAut.conj x • I : Subgroup G).subgroupOf H).subgroupOf
      ((MulAut.conj x • D : Subgroup G).subgroupOf H) := by
  ext d
  rw [MonoidHom.mem_ker, dxToQuot_apply, QuotientGroup.eq_one_iff]
  change x⁻¹ * ((d : H) : G) * x ∈ I ↔ _
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conj_smul_iff]

instance normal_subgroupOf_conj [(I.subgroupOf D).Normal] (x : G) :
    (((MulAut.conj x • I : Subgroup G).subgroupOf H).subgroupOf
      ((MulAut.conj x • D : Subgroup G).subgroupOf H)).Normal := by
  rw [← ker_dxToQuot (H := H) (D := D) (I := I) x]
  infer_instance

def dxQuotToQuot (H D I : Subgroup G) [(I.subgroupOf D).Normal] (x : G) :
    (MulAut.conj x • D : Subgroup G).subgroupOf H ⧸
        ((MulAut.conj x • I : Subgroup G).subgroupOf H).subgroupOf
          ((MulAut.conj x • D : Subgroup G).subgroupOf H) →*
      D ⧸ I.subgroupOf D :=
  QuotientGroup.lift _ (dxToQuot H D I x) (ker_dxToQuot x).symm.le

end GroundTheory.Global.Artin
