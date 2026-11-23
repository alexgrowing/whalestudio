import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV

noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

def iotaF (G : HTGroup p) (v : AwayP p) : Qv v ⊗[ℚ] G.F →ₐ[Qv v] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id (Qv v) (Qv v)) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem iotaF_tmul (G : HTGroup p) (v : AwayP p) (a : Qv v) (x : G.F) :
    iotaF G v (a ⊗ₜ[ℚ] x) = a ⊗ₜ[ℚ] algebraMap G.F G.C x := rfl

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact zero_mem _

theorem isIntV_add' (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add, Finsupp.add_apply]; exact add_mem (ha i) (hb i)

theorem isIntV_neg (G : HTGroup p) (v : AwayP p) {a : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a) :
    IsIntV G v (-a) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (ha i)

theorem isIntV_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (f : ι → Qv v ⊗[ℚ] G.C)
    (h : ∀ i ∈ s, IsIntV G v (f i)) : IsIntV G v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isIntV_zero G v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntV_add' G v (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

def intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Subring (Qv v ⊗[ℚ] G.F) where
  carrier := {m | IsIntV G v (iotaF G v m)}
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact h1
  mul_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_mul] at *; exact hm _ _ ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact isIntV_zero G v
  add_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_add] at *; exact isIntV_add' G v ha hb
  neg_mem' {a} ha := by simp only [Set.mem_setOf_eq, map_neg] at *; exact isIntV_neg G v ha

theorem mem_intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) (m : Qv v ⊗[ℚ] G.F) :
    m ∈ intF G v h1 hm ↔ IsIntV G v (iotaF G v m) := Iff.rfl

end GlobalTheory.OrbFinAf
