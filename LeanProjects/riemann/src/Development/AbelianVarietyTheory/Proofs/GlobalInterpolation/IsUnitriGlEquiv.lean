import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.UniIndexPrime

theorem diag_mul {k : ℕ} {A : Type} [CommRing A] {x y : Matrix (Fin k) (Fin k) A}
    (hx : ∀ i j, j < i → x i j = 0) (hy : ∀ i j, j < i → y i j = 0) (i : Fin k) :
    (x * y) i i = x i i * y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hx i j h, zero_mul]
  · rw [hy j i h, mul_zero]

def uniSub (k : ℕ) (A : Type) [CommRing A] : Subgroup (GL (Fin k) A) where
  carrier := upperUni k A
  one_mem' := fun i j => ⟨fun h => by simp [Matrix.one_apply_ne h.ne'], by simp⟩
  mul_mem' := by
    intro x y hx hy i j
    have bx : BlockTriangular (x : Matrix (Fin k) (Fin k) A) id := fun a b h => (hx a b).1 h
    have by' : BlockTriangular (y : Matrix (Fin k) (Fin k) A) id := fun a b h => (hy a b).1 h
    refine ⟨fun h => (bx.mul by') h, ?_⟩
    rw [Units.val_mul, diag_mul (fun a b h => (hx a b).1 h) (fun a b h => (hy a b).1 h),
      (hx i i).2, (hy i i).2, one_mul]
  inv_mem' := by
    intro x hx i j
    have bx : BlockTriangular (x : Matrix (Fin k) (Fin k) A) id := fun a b h => (hx a b).1 h
    letI : Invertible (x : Matrix (Fin k) (Fin k) A) := x.invertible
    have bi : BlockTriangular ((x⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) id := by
      rw [Matrix.coe_units_inv]
      exact blockTriangular_inv_of_blockTriangular bx
    refine ⟨fun h => bi h, ?_⟩
    have h := diag_mul (fun a b h => (hx a b).1 h) (fun a b h => bi (show id b < id a from h)) i
    rw [Units.mul_inv, (hx i i).2, one_mul] at h
    simpa using h.symm

theorem closure_eq (k : ℕ) (A : Type) [CommRing A] :
    Subgroup.closure (upperUni k A) = uniSub k A := Subgroup.closure_eq (uniSub k A)

theorem mem_uniSub {k : ℕ} {A : Type} [CommRing A] (x : GL (Fin k) A) :
    x ∈ uniSub k A ↔ IsUnitri (x : Matrix (Fin k) (Fin k) A) :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
    fun h i j => ⟨h.1 i j, h.2 i⟩⟩

def glEquiv (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    GL (Fin k) A ≃* GL (Fin k) B :=
  Units.mapEquiv (e.mapMatrix (m := Fin k)).toMulEquiv

theorem glEquiv_apply (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : GL (Fin k) A) (i j : Fin k) :
    (glEquiv k e x : Matrix (Fin k) (Fin k) B) i j = e ((x : Matrix (Fin k) (Fin k) A) i j) := rfl

theorem isUnitri_glEquiv (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : GL (Fin k) A) :
    IsUnitri (x : Matrix (Fin k) (Fin k) A) ↔
      IsUnitri (glEquiv k e x : Matrix (Fin k) (Fin k) B) := by
  simp only [IsUnitri, glEquiv_apply, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_one_iff]

theorem index_upperUni : ∀ (κ : Type) [CommRing κ] (g k : ℕ), g.Prime → Nat.card κ = g →
    (((Subgroup.closure (upperUni k κ)).index : ℕ) : ℝ) = idxColLoc g k := by
  intro κ _ g k hg hc
  haveI : Finite κ := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
  letI : Fintype κ := Fintype.ofFinite κ
  have e : ZMod g ≃+* κ := ZMod.ringEquivOfPrime κ hg (by rw [← Nat.card_eq_fintype_card, hc])
  have h1 : Nat.card (GL (Fin k) (ZMod g)) = Nat.card (GL (Fin k) κ) :=
    Nat.card_congr (glEquiv k e).toEquiv
  have h2 : Nat.card {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      Nat.card (uniSub k κ) :=
    Nat.card_congr ((glEquiv k e).toEquiv.subtypeEquiv fun x =>
      (isUnitri_glEquiv k e x).trans (mem_uniSub _).symm)
  have h3 : (Nat.card (uniSub k κ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := uniSub k κ)).ne'
  rw [closure_eq, idxColLoc, idxLoc, h1, h2, eq_div_iff h3]
  exact_mod_cast (uniSub k κ).index_mul_card

end GlobalTheory.UniIndexPrime
