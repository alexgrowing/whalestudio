import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaA

open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaMat

variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

def fIwasawaP (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => if π i = j then 1 else 0

theorem permMatrix_mulVec₂ (π : Equiv.Perm (Fin n)) (w : Fin n → L) :
    fIwasawaP π *ᵥ w = fun i => w (π i) := by
  funext i
  simp [fIwasawaP, Matrix.mulVec, dotProduct]

theorem permMatrix_mul_apply₂ (π : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (fIwasawaP π * M : Matrix (Fin n) (Fin n) L) i j = M (π i) j := by
  simp [fIwasawaP, Matrix.mul_apply]

theorem permMatrix_isUnitary_of_commute_rev (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (Fin.rev i) = Fin.rev (π i)) :
    fIwasawaUn σ (fIwasawaP (L := L) π) := by
  apply fIwasawa_un_of_isometry
  intro x y
  simp only [fIwasawaH, permMatrix_mulVec₂, hπ]
  exact Equiv.sum_comp π (fun k => σ (x (Fin.rev k)) * y k)

def fIwasawaE (e z : Fin n → L) (c : L) : Matrix (Fin n) (Fin n) L :=
  Matrix.of fun i j => (if i = j then 1 else 0) + z i * σ (e (Fin.rev j)) - e i * σ (z (Fin.rev j)) +
    c * e i * σ (e (Fin.rev j))

theorem fIwasawa_E_mulVec (e z : Fin n → L) (c : L) (w : Fin n → L) :
    fIwasawaE σ e z c *ᵥ w = w + fIwasawaH σ e w • z - fIwasawaH σ z w • e +
      (c * fIwasawaH σ e w) • e := by
  funext i
  simp only [fIwasawaE, fIwasawaH, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum, Finset.sum_mul]
  ring_nf

theorem fIwasawa_E_un (hσ : ∀ x, σ (σ x) = x) (e z : Fin n → L) (c : L)
    (hee : fIwasawaH σ e e = 0) (hez : fIwasawaH σ e z = 0)
    (hc : c + σ c + fIwasawaH σ z z = 0) : fIwasawaUn σ (fIwasawaE σ e z c) := by
  have Hal : ∀ x x' y : Fin n → L, fIwasawaH σ (x + x') y = fIwasawaH σ x y + fIwasawaH σ x' y := by
    intro x x' y
    simp [fIwasawaH, add_mul, Finset.sum_add_distrib]
  have Hsl : ∀ x x' y : Fin n → L, fIwasawaH σ (x - x') y = fIwasawaH σ x y - fIwasawaH σ x' y := by
    intro x x' y
    simp [fIwasawaH, sub_mul, Finset.sum_sub_distrib]
  have Hml : ∀ (t : L) (x y : Fin n → L), fIwasawaH σ (t • x) y = σ t * fIwasawaH σ x y := by
    intro t x y
    simp [fIwasawaH, Finset.mul_sum, mul_assoc]
  have Har : ∀ x y y' : Fin n → L, fIwasawaH σ x (y + y') = fIwasawaH σ x y + fIwasawaH σ x y' := by
    intro x y y'
    simp [fIwasawaH, mul_add, Finset.sum_add_distrib]
  have Hsr : ∀ x y y' : Fin n → L, fIwasawaH σ x (y - y') = fIwasawaH σ x y - fIwasawaH σ x y' := by
    intro x y y'
    simp [fIwasawaH, mul_sub, Finset.sum_sub_distrib]
  have Hmr : ∀ (t : L) (x y : Fin n → L), fIwasawaH σ x (t • y) = t * fIwasawaH σ x y := by
    intro t x y
    simp only [fIwasawaH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have Hsym : ∀ x y : Fin n → L, fIwasawaH σ y x = σ (fIwasawaH σ x y) := by
    intro x y
    simp only [fIwasawaH, map_sum, map_mul, hσ]
    exact (Fintype.sum_equiv Fin.revPerm _ _ fun j => by simp [mul_comm]).symm
  apply fIwasawa_un_of_isometry
  intro w w'
  rw [fIwasawa_E_mulVec, fIwasawa_E_mulVec]
  simp only [Hal, Hsl, Hml, Har, Hsr, Hmr, map_mul]
  simp only [Hsym z w, Hsym e w, Hsym e z, hez, hee, map_zero]
  linear_combination (σ (fIwasawaH σ e w) * fIwasawaH σ e w') * hc

end FIwasawaMat

section FIwasawaInt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

def fIwasawaInt (M : Matrix (Fin n) (Fin n) L) : Prop := ∀ i j, Valued.v (M i j) ≤ 1

theorem fIwasawa_int_mul (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaInt A) (hB : fIwasawaInt B) :
    fIwasawaInt (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [map_mul]; exact mul_le_one' (hA i k) (hB k j)

theorem fIwasawa_int_one : fIwasawaInt (1 : Matrix (Fin n) (Fin n) L) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem fIwasawa_int_inv (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaInt M) : fIwasawaInt (fIwasawaInv σ M) := by
  have hJ : fIwasawaInt (antiJ L n) := by
    intro i j
    simp only [antiJ]
    split_ifs <;> simp
  have hcT : fIwasawaInt (cT σ M) := by
    intro i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [hσv]
    exact hM j i
  unfold fIwasawaInv
  exact fIwasawa_int_mul _ _ (fIwasawa_int_mul _ _ hJ hcT) hJ

theorem fIwasawa_int_P (π : Equiv.Perm (Fin n)) : fIwasawaInt (fIwasawaP (L := L) π) := by
  intro i j
  simp only [fIwasawaP, Matrix.of_apply]
  split_ifs <;> simp

theorem fIwasawa_int_E (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (e z : Fin n → L) (c : L)
    (he : ∀ i, Valued.v (e i) ≤ 1) (hz : ∀ i, Valued.v (z i) ≤ 1) (hc : Valued.v c ≤ 1) :
    fIwasawaInt (fIwasawaE σ e z c) := by
  intro i j
  simp only [fIwasawaE, Matrix.of_apply]
  have h1 : Valued.v (if i = j then (1 : L) else 0) ≤ 1 := by split_ifs <;> simp
  refine Valuation.map_add_le _ (Valuation.map_sub_le _ (Valuation.map_add_le _ h1 ?_) ?_) ?_
  · rw [map_mul, hσv]
    exact mul_le_one' (hz i) (he _)
  · rw [map_mul, hσv]
    exact mul_le_one' (he i) (hz _)
  · rw [map_mul, map_mul, hσv]
    exact mul_le_one' (mul_le_one' hc (he i)) (he _)

theorem fIwasawa_mk_mem_K (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaUn σ M) (hI : fIwasawaInt M) : fIwasawaMk σ M hM ∈ KU σ n := by
  have hinvI := fIwasawa_int_inv σ hσv M hI
  rw [KU, Subgroup.mem_subgroupOf]
  refine Subgroup.mem_inf.2 ⟨(fIwasawaMk σ M hM).2, ?_⟩
  let A : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨M i j, hI i j⟩
  let B : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨fIwasawaInv σ M i j, hinvI i j⟩
  have hinj : Function.Injective
      (RingHom.mapMatrix (intL L).subtype : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have hA : RingHom.mapMatrix (intL L).subtype A = M := by ext i j; rfl
  have hB : RingHom.mapMatrix (intL L).subtype B = fIwasawaInv σ M := by ext i j; rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, hA, hB, map_one, fIwasawa_mul_inv σ M hM])
  have hBA : B * A = 1 := hinj (by rw [map_mul, hA, hB, map_one, fIwasawa_inv_mul σ M hM])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  show RingHom.mapMatrix (intL L).subtype A = _
  rw [hA]
  exact (fIwasawa_mk_val σ M hM).symm

theorem fIwasawa_K_int (k : GU σ n) (hk : k ∈ KU σ n) :
    fIwasawaInt (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
  intro i j
  have h1 := Subgroup.mem_subgroupOf.1 hk
  obtain ⟨k', hk'⟩ := (Subgroup.mem_inf.1 h1).2
  rw [← hk']
  show Valued.v (((k' : Matrix (Fin n) (Fin n) (intL L)) i j : intL L) : L) ≤ 1
  exact (k' i j).2

end FIwasawaInt

end Formalism.UG.P
