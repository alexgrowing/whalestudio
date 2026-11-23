import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.SlPLaws
open MvPolynomial

variable {R : Type} [CommRing R]

theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (X i) = (m i 0 : R) • X 0 + (m i 1 : R) • X 1 := by
  simp [slP]

theorem polySlash_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP (m * m') p = slP m' (slP m p) := by
  have h : (slP (R := R) (m * m')) = (slP m').comp (slP m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add, map_smul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    simp only [smul_add, add_smul, smul_smul, mul_comm]
    abel
  rw [h]; rfl

theorem polySlash_one' (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h : (slP (R := R) 1) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [h]; rfl

theorem polySlash_isHomogeneous (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R)
    (hp : p.IsHomogeneous w) : (slP m p).IsHomogeneous w := by
  have := IsHomogeneous.aeval (τ := Fin 2) (S := R) (n := 1) hp (fun i => (m i 0 : R) • X 0 + (m i 1 : R) • X 1) (fun i => by
    apply IsHomogeneous.add
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 0).C_mul _
    · rw [smul_eq_C_mul]; exact (isHomogeneous_X R 1).C_mul _)
  rw [one_mul] at this
  simpa [slP] using this

theorem eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    eval u (slP m p) = eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, eval_X]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem map_slP {S : Type} [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, map_X, map_add]
    simp [MvPolynomial.smul_eq_C_mul]

theorem polySlash_congr (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R)
    (h : ∀ i j, (m i j : R) = (m' i j : R)) : slP m p = slP m' p := by
  simp only [slP, h]

theorem polySlash_neg_one (w : ℕ) (p : MvPolynomial (Fin 2) R) (hp : p.IsHomogeneous w) :
    slP (-1) p = (-1 : R) ^ w • p := by
  have e : (slP (R := R) (-1)) = aeval fun i => (-1 : R) • X i := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [slP_X]
  rw [e]
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hw := hp (mem_support_iff.mp hv)
  rw [aeval_monomial]
  simp only [smul_pow, Finsupp.prod_pow]
  have hw' : v 0 + v 1 = w := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]; simp
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, ← hw']
  simp only [smul_eq_C_mul, algebraMap_eq, pow_add, map_mul, map_pow, map_neg, map_one]
  ring

end GlobalTheory.KZ.SlPLaws

namespace GlobalTheory.KZ

theorem polySlash_laws : ∀ (R : Type) [CommRing R], (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), slP (m * m') p = slP m' (slP m p)) ∧ (∀ p : MvPolynomial (Fin 2) R, slP 1 p = p) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → (slP m p).IsHomogeneous w) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R), MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p)) ∧ (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), (∀ i j, (m i j : R) = (m' i j : R)) → slP m p = slP m' p) ∧ (∀ (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → slP (-1) p = (-1 : R) ^ w • p) := by
  intro R _
  exact ⟨SlPLaws.polySlash_mul, SlPLaws.polySlash_one', SlPLaws.polySlash_isHomogeneous, SlPLaws.eval_slP, fun S _ f => SlPLaws.map_slP f,
    fun m m' p h => SlPLaws.polySlash_congr m m' p h, fun w p hp => SlPLaws.polySlash_neg_one w p hp⟩

end GlobalTheory.KZ
