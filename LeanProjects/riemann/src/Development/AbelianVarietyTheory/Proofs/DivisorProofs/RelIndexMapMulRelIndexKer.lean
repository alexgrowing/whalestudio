import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory

theorem addSubgroup_relIndex_split {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (g : M →+ N) (a b : AddSubgroup M) (hab : a ≤ b) :
    a.relIndex b = (a.map g).relIndex (b.map g) * (a ⊓ g.ker).relIndex (b ⊓ g.ker) := by
  set m : AddSubgroup M := a ⊔ (b ⊓ g.ker) with hm
  have ham : a ≤ m := le_sup_left
  have hmb : m ≤ b := sup_le hab inf_le_left
  have hmeq : m = b ⊓ (a.map g).comap g := by
    ext x
    simp only [hm, AddSubgroup.mem_sup, AddSubgroup.mem_inf, AddSubgroup.mem_comap,
      AddSubgroup.mem_map, AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨y, hy, z, ⟨hzb, hzk⟩, rfl⟩
      exact ⟨b.add_mem (hab hy) hzb, y, hy, by simp [hzk]⟩
    · rintro ⟨hxb, y, hy, hyx⟩
      refine ⟨y, hy, x - y, ⟨b.sub_mem hxb (hab hy), by simp [hyx]⟩, by abel⟩
  have h1 : m.relIndex b = (a.map g).relIndex (b.map g) := by
    rw [hmeq, inf_comm, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  have h2 : a.relIndex m = (a ⊓ g.ker).relIndex (b ⊓ g.ker) := by
    rw [hm, sup_comm, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right,
      ← AddSubgroup.inf_relIndex_right (a ⊓ g.ker)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    constructor
    · rintro ⟨ha, hb, hk⟩; exact ⟨⟨ha, hk⟩, hb, hk⟩
    · rintro ⟨⟨ha, hk⟩, hb, -⟩; exact ⟨ha, hb, hk⟩
  have h3 := AddSubgroup.relIndex_mul_relIndex a m b ham hmb
  rw [h1, h2] at h3
  rw [← h3, mul_comm]

theorem submodule_relIndex_split {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (A B : Submodule R M) (hAB : A ≤ B) :
    A.toAddSubgroup.relIndex B.toAddSubgroup =
      (A.map f).toAddSubgroup.relIndex (B.map f).toAddSubgroup *
        (A ⊓ LinearMap.ker f).toAddSubgroup.relIndex (B ⊓ LinearMap.ker f).toAddSubgroup := by
  have hk : (LinearMap.ker f).toAddSubgroup = f.toAddMonoidHom.ker := by
    ext x; simp
  have hmap : ∀ P : Submodule R M, (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom := by
    intro P; ext x; simp
  have hinf : ∀ P Q : Submodule R M, (P ⊓ Q).toAddSubgroup = P.toAddSubgroup ⊓ Q.toAddSubgroup := by
    intro P Q; ext x; simp
  rw [hmap, hmap, hinf, hinf, hk]
  exact addSubgroup_relIndex_split f.toAddMonoidHom _ _ hAB

end GlobalTheory
