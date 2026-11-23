import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section ConjInvariance

variable {H : Type} [Group H]

theorem mem_map_conj_iff (B : Subgroup H) (x y : H) :
    y ∈ B.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * y * x ∈ B := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mul_assoc] using hz
  · intro hy
    exact ⟨x⁻¹ * y * x, hy, by simp [mul_assoc]⟩

theorem map_conj_mul (B : Subgroup H) (x s : H) :
    (B.map (MulAut.conj s).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      B.map (MulAut.conj (x * s)).toMonoidHom := by
  ext y
  simp only [mem_map_conj_iff, mul_inv_rev]
  simp [mul_assoc]

def stabInv (A B : Subgroup H) (x : H) : ℚ :=
  ((Nat.card (A ⊓ B.map (MulAut.conj x).toMonoidHom : Subgroup H) : ℕ) : ℚ)⁻¹

theorem stabInv_mul (A B : Subgroup H) (x : H) {a b : H} (ha : a ∈ A) (hb : b ∈ B) :
    stabInv A B (a * x * b) = stabInv A B x := by
  unfold stabInv
  have e : (A ⊓ B.map (MulAut.conj (a * x * b)).toMonoidHom : Subgroup H) =
      (A ⊓ B.map (MulAut.conj x).toMonoidHom : Subgroup H).map (MulAut.conj a).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_inf, mem_map_conj_iff]
    constructor
    · rintro ⟨hyA, hyB⟩
      refine ⟨A.mul_mem (A.mul_mem (A.inv_mem ha) hyA) ha, ?_⟩
      have := B.mul_mem (B.mul_mem hb hyB) (B.inv_mem hb)
      convert this using 1
      group
    · rintro ⟨hzA, hzB⟩
      refine ⟨?_, ?_⟩
      · have := A.mul_mem (A.mul_mem ha hzA) (A.inv_mem ha)
        convert this using 1
        group
      · have := B.mul_mem (B.mul_mem (B.inv_mem hb) hzB) hb
        convert this using 1
        group
  rw [e, Nat.card_congr ((A ⊓ B.map (MulAut.conj x).toMonoidHom).equivMapOfInjective _
    (MulAut.conj a).injective).toEquiv.symm]

theorem stabInv_eq_of_mk_eq (A B : Subgroup H) {x y : H}
    (h : DoubleCoset.mk A B x = DoubleCoset.mk A B y) : stabInv A B x = stabInv A B y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 h
  exact (stabInv_mul A B x ha hb).symm

def dcMulRight (A B : Subgroup H) (s : H) :
    DoubleCoset.Quotient (A : Set H) ((B.map (MulAut.conj s).toMonoidHom : Subgroup H) : Set H) ≃
      DoubleCoset.Quotient (A : Set H) (B : Set H) :=
  Quotient.congr (Equiv.mulRight s) (by
    intro x y
    rw [← DoubleCoset.eq'', ← DoubleCoset.eq'', DoubleCoset.eq, DoubleCoset.eq]
    simp only [Equiv.coe_mulRight, mem_map_conj_iff]
    constructor
    · rintro ⟨a, ha, k, hk, rfl⟩
      exact ⟨a, ha, s⁻¹ * k * s, hk, by simp [mul_assoc]⟩
    · rintro ⟨a, ha, k, hk, e⟩
      refine ⟨a, ha, s * k * s⁻¹, by simpa [mul_assoc] using hk, ?_⟩
      have := congrArg (· * s⁻¹) e
      simpa [mul_assoc] using this)

theorem dcMulRight_mk (A B : Subgroup H) (s x : H) :
    dcMulRight A B s (DoubleCoset.mk A (B.map (MulAut.conj s).toMonoidHom) x) =
      DoubleCoset.mk A B (x * s) := rfl

theorem finsum_stabInv_conj (A B : Subgroup H) (s : H) :
    (∑ᶠ q : DoubleCoset.Quotient (A : Set H) ((B.map (MulAut.conj s).toMonoidHom : Subgroup H) : Set H),
      stabInv A (B.map (MulAut.conj s).toMonoidHom) (Quotient.out q)) =
    ∑ᶠ q : DoubleCoset.Quotient (A : Set H) (B : Set H), stabInv A B (Quotient.out q) := by
  rw [← finsum_comp_equiv (dcMulRight A B s)]
  refine finsum_congr fun q => ?_
  unfold stabInv
  rw [map_conj_mul]
  refine stabInv_eq_of_mk_eq A B ?_
  rw [← dcMulRight_mk, DoubleCoset.out_eq', DoubleCoset.out_eq']

end ConjInvariance

theorem massC_map_conj : ∀ {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G), t ∈ T → C ≤ T →
    massC Γ' T (C.map (MulAut.conj t).toMonoidHom) = massC Γ' T C := by
  intro G _ Γ' T C t ht _
  have hsub : (C.map (MulAut.conj t).toMonoidHom).subgroupOf T =
      (C.subgroupOf T).map (MulAut.conj (⟨t, ht⟩ : T)).toMonoidHom := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_map_conj_iff, mem_map_conj_iff, Subgroup.mem_subgroupOf]
    simp
  unfold massC
  rw [hsub]
  exact finsum_stabInv_conj _ _ _

end GlobalTheory.LKCount
