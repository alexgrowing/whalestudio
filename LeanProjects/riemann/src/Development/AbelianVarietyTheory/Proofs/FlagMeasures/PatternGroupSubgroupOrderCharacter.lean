import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.Pattern

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
theorem _root_.GlobalTheory.GLm.Pattern.inPat_mul {Φ : Fin N → Fin N → Prop}
    (ht : ∀ a b c, Φ a b → Φ b c → Φ a c) {M M' : _root_.GlobalTheory.GLq.Mt g N}
    (h : _root_.GlobalTheory.GLm.InPat Φ M) (h' : _root_.GlobalTheory.GLm.InPat Φ M') :
    _root_.GlobalTheory.GLm.InPat Φ (M * M') := by
  intro a b hab
  have hone : (1 : _root_.GlobalTheory.GLq.Mt g N) a b =
      ((1 : _root_.GlobalTheory.GLq.Mt g N) * 1) a b := by rw [one_mul]
  rw [hone, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hac : Φ a c
  · have hcb : ¬ Φ c b := fun hcb => hab (ht a c b hac hcb)
    rw [h' c b hcb]
    by_cases e : c = b
    · subst e; exact absurd hac hab
    · rw [Matrix.one_apply_ne e, mul_zero, mul_zero]
  · rw [h a c hac]
    by_cases e : a = c
    · subst e; rw [h' a b hab]
    · rw [Matrix.one_apply_ne e, zero_mul, zero_mul]

def patSub (g : ℕ) [Fact g.Prime] {N : ℕ} (Φ : Fin N → Fin N → Prop)
    (ht : ∀ a b c, Φ a b → Φ b c → Φ a c) : Subgroup (Gn g N) where
  carrier := {x | InPat Φ (x : Mt g N)}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun ha hb => inPat_mul ht ha hb
  inv_mem' := by
    intro x hx
    have hp : ∀ k : ℕ, InPat Φ ((x ^ k : Gn g N) : Mt g N) := by
      intro k
      induction k with
      | zero => exact fun _ _ _ => rfl
      | succ k ih => rw [pow_succ]; exact inPat_mul ht ih hx
    have ho : 0 < orderOf x := orderOf_pos x
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel ho, pow_orderOf_eq_one]
    show InPat Φ ((x⁻¹ : Gn g N) : Mt g N)
    rw [this]; exact hp _

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
private theorem isUnit_of_inPat_irrefl_trans {Φ : Fin N → Fin N → Prop} (hirr : ∀ a, ¬ Φ a a)
    (htrans : ∀ a b c, Φ a b → Φ b c → Φ a c) {M : _root_.GlobalTheory.GLq.Mt g N}
    (h : _root_.GlobalTheory.GLm.InPat Φ M) : IsUnit M := by
  let r : Fin N → ℕ := fun i => (Finset.univ.filter fun j => Φ j i).card
  have hr : ∀ i j, Φ i j → r i < r j := by
    intro i j hij
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, by simp [hij], by simp [hirr i]⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact htrans k i j hk hij
  have hbt : Matrix.BlockTriangular M r := by
    intro i j hji
    have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hji
    rw [h i j (fun hij => absurd (hr i j hij) (not_lt.mpr hji.le)), Matrix.one_apply_ne hne]
  have hblock : ∀ k, Matrix.toSquareBlock M r k = 1 := by
    intro k
    refine Matrix.ext fun i j => ?_
    rw [Matrix.toSquareBlock_def, Matrix.of_apply]
    have hij : ¬ Φ i.1 j.1 := fun hij => (hr _ _ hij).ne (i.2.trans j.2.symm)
    rw [h _ _ hij]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun h => e (Subtype.ext h))]
  rw [Matrix.isUnit_iff_isUnit_det, hbt.det]
  simp [hblock]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in

theorem _root_.GlobalTheory.GLm.Pattern.pattern_group : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ)
    (Φ : Fin N → Fin N → Prop), (∀ a, ¬ Φ a a) → (∀ a b c, Φ a b → Φ b c → Φ a c) →
    (∃ H : Subgroup (_root_.GlobalTheory.GLq.Gn g N),
      (∀ x, x ∈ H ↔ _root_.GlobalTheory.GLm.InPat Φ (x : _root_.GlobalTheory.GLq.Mt g N)) ∧
      Nat.card H = g ^ (Finset.univ.filter fun p : Fin N × Fin N => Φ p.1 p.2).card) ∧
    (∀ M : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M → IsUnit M) ∧
    ∀ E : Fin N → Fin N → Prop, (∀ a b c, Φ a b → Φ b c → ¬ E a c) → (∀ a, ¬ E a a) →
      ∀ M M' : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M →
        _root_.GlobalTheory.GLm.InPat Φ M' →
        _root_.GlobalTheory.GLm.sumAt E (M * M') =
          _root_.GlobalTheory.GLm.sumAt E M + _root_.GlobalTheory.GLm.sumAt E M' := by
  intro g _ N Φ hirr htrans
  have hunit : ∀ M : _root_.GlobalTheory.GLq.Mt g N, _root_.GlobalTheory.GLm.InPat Φ M → IsUnit M :=
    fun M hM => isUnit_of_inPat_irrefl_trans hirr htrans hM
  refine ⟨⟨_root_.GlobalTheory.GLm.Pattern.patSub g Φ htrans, fun x => Iff.rfl, ?_⟩, hunit, ?_⟩
  · have e1 : Nat.card (_root_.GlobalTheory.GLm.Pattern.patSub g Φ htrans) =
        Nat.card {M : _root_.GlobalTheory.GLq.Mt g N // _root_.GlobalTheory.GLm.InPat Φ M} := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun x => ⟨(x.1 : _root_.GlobalTheory.GLq.Mt g N), x.2⟩) ⟨?_, ?_⟩)
      · intro x y hxy
        exact Subtype.ext (Units.ext (congrArg Subtype.val hxy))
      · intro M
        exact ⟨⟨(hunit M.1 M.2).unit, M.2⟩, rfl⟩
    let e2 : {M : _root_.GlobalTheory.GLq.Mt g N // _root_.GlobalTheory.GLm.InPat Φ M} ≃
        ({p : Fin N × Fin N // Φ p.1 p.2} → ZMod g) :=
      { toFun := fun M p => M.1 p.1.1 p.1.2
        invFun := fun f => ⟨fun a b => if h : Φ a b then f ⟨(a, b), h⟩
            else (1 : _root_.GlobalTheory.GLq.Mt g N) a b, fun a b h => by simp [h]⟩
        left_inv := fun M => by
          apply Subtype.ext
          refine Matrix.ext fun a b => ?_
          dsimp only
          split_ifs with h
          · rfl
          · exact (M.2 a b h).symm
        right_inv := fun f => by
          funext p
          simp [p.2] }
    rw [e1, Nat.card_congr e2, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  · intro E hE hEirr M M' hM hM'
    unfold _root_.GlobalTheory.GLm.sumAt
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hac
    · rw [Matrix.mul_apply]
      have hne : a ≠ c := by rintro rfl; exact hEirr a hac
      rw [Fintype.sum_eq_add a c hne]
      · rw [hM a a (hirr a), hM' c c (hirr c), Matrix.one_apply_eq, Matrix.one_apply_eq,
          one_mul, mul_one, add_comm]
      · rintro b ⟨hba, hbc⟩
        by_cases hab : Φ a b
        · rw [hM' b c (fun hbc' => hE a b c hab hbc' hac), Matrix.one_apply_ne hbc, mul_zero]
        · rw [hM a b hab, Matrix.one_apply_ne (Ne.symm hba), zero_mul]
    · simp

end GlobalTheory.GLm.Pattern
