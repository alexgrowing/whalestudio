import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.PfaffBlock

open Equiv Finset

theorem alt_antisymm {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (α : T [⋀^Fin 2]→L[ℝ] ℝ) (u w : T) : α ![u, w] = -α ![w, u] := by
  have h := α.toAlternatingMap.map_swap ![w, u] (i := 0) (j := 1) (by decide)
  have e : (![w, u] ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![u, w] := by
    ext i; fin_cases i <;> rfl
  rw [e] at h
  simpa using h

theorem sum_perm_fin_two (f : Perm (Fin 2) → ℝ) : ∑ c, f c = f 1 + f (swap 0 1) := by
  have : (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} := by decide
  rw [this, Finset.sum_pair (by decide)]

theorem sum_sign_prod_split {g : ℕ} (A A' : Fin g × Fin 2 → Fin g × Fin 2 → ℝ)
    (hA : ∀ x y, A x y = A' x y - A' y x) :
    ∑ σ : Perm (Fin g × Fin 2), ((Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ (i, 0)) (σ (i, 1)) =
      2 ^ g * ∑ σ : Perm (Fin g × Fin 2),
        ((Perm.sign σ : ℤ) : ℝ) * ∏ i, A' (σ (i, 0)) (σ (i, 1)) := by
  have h2 : ∀ (σ : Perm (Fin g × Fin 2)) i, A (σ (i, 0)) (σ (i, 1)) =
      ∑ c : Perm (Fin 2), ((Perm.sign c : ℤ) : ℝ) * A' (σ (i, c 0)) (σ (i, c 1)) := by
    intro σ i
    rw [hA, sum_perm_fin_two, Perm.sign_swap (by decide)]
    simp [sub_eq_add_neg]
  have key : ∀ σ : Perm (Fin g × Fin 2), ∏ i, A (σ (i, 0)) (σ (i, 1)) =
      ∑ C : Fin g → Perm (Fin 2), ((Perm.sign (prodCongrRight C) : ℤ) : ℝ) *
        ∏ i, A' ((σ * prodCongrRight C) (i, 0)) ((σ * prodCongrRight C) (i, 1)) := by
    intro σ
    simp_rw [h2 σ, Finset.prod_univ_sum, Perm.sign_prodCongrRight]
    refine Finset.sum_congr rfl fun C _ => ?_
    simp [Finset.prod_mul_distrib, Perm.mul_apply, prodCongrRight_apply]
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hC : ∀ C : Fin g → Perm (Fin 2),
      ∑ σ : Perm (Fin g × Fin 2), ((Perm.sign σ : ℤ) : ℝ) *
        (((Perm.sign (prodCongrRight C) : ℤ) : ℝ) *
          ∏ i, A' ((σ * prodCongrRight C) (i, 0)) ((σ * prodCongrRight C) (i, 1))) =
      ∑ σ : Perm (Fin g × Fin 2), ((Perm.sign σ : ℤ) : ℝ) * ∏ i, A' (σ (i, 0)) (σ (i, 1)) := by
    intro C
    refine Fintype.sum_equiv (Equiv.mulRight (prodCongrRight C)) _ _ (fun σ => ?_)
    simp only [Equiv.coe_mulRight, Perm.sign_mul, Units.val_mul, Int.cast_mul]
    ring
  rw [Finset.sum_congr rfl fun C _ => hC C, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_perm, nsmul_eq_mul]
  simp [Finset.mul_sum]

def half {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) (x y : Fin g × Fin 2) : ℝ :=
  if x.2 = 0 ∧ y.2 = 1 then S x.1 y.1 else 0

def colPerm {g : ℕ} (p : Perm (Fin g) × Perm (Fin g)) : Perm (Fin g × Fin 2) :=
  prodCongrLeft fun c => if c = 0 then p.1 else p.2

theorem colPerm_injective {g : ℕ} : Function.Injective (colPerm (g := g)) := by
  intro p q h
  have h0 : ∀ i, p.1 i = q.1 i := fun i => by
    have := congrArg (fun s : Perm (Fin g × Fin 2) => (s (i, 0)).1) h
    simpa [colPerm] using this
  have h1 : ∀ i, p.2 i = q.2 i := fun i => by
    have := congrArg (fun s : Perm (Fin g × Fin 2) => (s (i, 1)).1) h
    simpa [colPerm] using this
  exact Prod.ext (Equiv.ext h0) (Equiv.ext h1)

theorem half_term_eq_zero {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) (σ : Perm (Fin g × Fin 2))
    (hσ : σ ∉ Finset.univ.image (colPerm (g := g))) :
    ((Perm.sign σ : ℤ) : ℝ) * ∏ i, half S (σ (i, 0)) (σ (i, 1)) = 0 := by
  by_contra hne
  have hprod : ∏ i, half S (σ (i, 0)) (σ (i, 1)) ≠ 0 := right_ne_zero_of_mul hne
  have hcol : ∀ i, (σ (i, 0)).2 = 0 ∧ (σ (i, 1)).2 = 1 := by
    intro i
    have := Finset.prod_ne_zero_iff.1 hprod i (Finset.mem_univ _)
    unfold half at this
    by_contra h
    exact this (if_neg h)
  have hinj : ∀ c : Fin 2, Function.Injective fun i => (σ (i, c)).1 := by
    intro c i j hij
    have hc : (σ (i, c)).2 = (σ (j, c)).2 := by
      fin_cases c
      · simp [(hcol i).1, (hcol j).1]
      · simp [(hcol i).2, (hcol j).2]
    have := σ.injective (Prod.ext hij hc)
    exact congrArg Prod.fst this
  let a : Perm (Fin g) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (hinj 0))
  let b : Perm (Fin g) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (hinj 1))
  apply hσ
  refine Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, ?_⟩
  ext ⟨i, c⟩
  · fin_cases c <;> simp [colPerm, a, b]
  · fin_cases c
    · simp [colPerm, (hcol i).1]
    · simp [colPerm, (hcol i).2]

theorem half_term_colPerm {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) (p : Perm (Fin g) × Perm (Fin g)) :
    ((Perm.sign (colPerm p) : ℤ) : ℝ) * ∏ i, half S (colPerm p (i, 0)) (colPerm p (i, 1)) =
      ((Perm.sign p.1 : ℤ) : ℝ) * ((Perm.sign p.2 : ℤ) : ℝ) * ∏ i, S (p.1 i) (p.2 i) := by
  simp [colPerm, half, Perm.sign_prodCongrLeft, Fin.prod_univ_two]

theorem sum_half {g : ℕ} (S : Matrix (Fin g) (Fin g) ℝ) :
    ∑ σ : Perm (Fin g × Fin 2), ((Perm.sign σ : ℤ) : ℝ) * ∏ i, half S (σ (i, 0)) (σ (i, 1)) =
      (g.factorial : ℝ) * S.det := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (colPerm (g := g))))
      (fun σ _ hσ => half_term_eq_zero S σ hσ),
    Finset.sum_image (fun p _ q _ h => colPerm_injective h)]
  simp_rw [half_term_colPerm]
  rw [Fintype.sum_prod_type]
  have inner : ∀ a : Perm (Fin g), ∑ b : Perm (Fin g),
      ((Perm.sign a : ℤ) : ℝ) * ((Perm.sign b : ℤ) : ℝ) * ∏ i, S (a i) (b i) = S.det := by
    intro a
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine (Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun c => ?_)).symm
    simp only [Equiv.coe_mulRight, Perm.mul_apply, Matrix.transpose_apply]
    rw [Equiv.prod_comp a (fun j => S j (c j))]
    have hs : ((Perm.sign a : ℤ) : ℝ) * ((Perm.sign (c * a) : ℤ) : ℝ) = ((Perm.sign c : ℤ) : ℝ) := by
      rw [Perm.sign_mul, ← Int.cast_mul, ← Units.val_mul, mul_comm (Perm.sign c), ← mul_assoc,
        Int.units_mul_self, one_mul]
    rw [hs]
  simp_rw [inner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end GlobalTheory.PfaffBlock

namespace GlobalTheory

open GlobalTheory.PfaffBlock

theorem wedgePow_block_eq {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (α : T [⋀^Fin 2]→L[ℝ] ℝ) (g : ℕ) (v : Fin g × Fin 2 → T) (S : Matrix (Fin g) (Fin g) ℝ)
    (h0 : ∀ i j, α ![v (i, 0), v (j, 0)] = 0) (h1 : ∀ i j, α ![v (i, 1), v (j, 1)] = 0)
    (h01 : ∀ i j, α ![v (i, 0), v (j, 1)] = S i j) :
    wedgePow α g v = (g.factorial : ℝ) * S.det := by
  have hA : ∀ x y, α ![v x, v y] = half S x y - half S y x := by
    rintro ⟨i, c⟩ ⟨j, d⟩
    fin_cases c <;> fin_cases d
    · simp [half, h0]
    · simp [half, h01]
    · simp [half, alt_antisymm α (v (i, 1)), h01]
    · simp [half, h1]
  unfold wedgePow
  rw [sum_sign_prod_split (fun x y => α ![v x, v y]) (half S) hA, sum_half, ← mul_assoc,
    one_div, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_mul]

example : ∀ {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] (α : T [⋀^Fin 2]→L[ℝ] ℝ) (g : ℕ)
    (v : Fin g × Fin 2 → T) (S : Matrix (Fin g) (Fin g) ℝ), (∀ i j, α ![v (i, 0), v (j, 0)] = 0) →
    (∀ i j, α ![v (i, 1), v (j, 1)] = 0) → (∀ i j, α ![v (i, 0), v (j, 1)] = S i j) →
    wedgePow α g v = (g.factorial : ℝ) * S.det :=
  fun α g v S => wedgePow_block_eq α g v S

end GlobalTheory
