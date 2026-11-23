import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.FischerAdjointnessHolds
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW

section general

variable (R : Type) [CommRing R] {r n : ℕ}

theorem rgl_swp_apply (f : MvPolynomial (Fin r × Fin n) R) :
    swp R r n f = rename (Equiv.prodComm (Fin r) (Fin n)) f := rfl

theorem rgl_swp_X (a : Fin r) (s : Fin n) : swp R r n (X (a, s)) = X (s, a) := by
  rw [rgl_swp_apply, rename_X]; rfl

theorem rgl_swp_C (c : R) : swp R r n (C c) = C c := by
  rw [rgl_swp_apply, rename_C]

theorem rgl_swp_map {S : Type} [CommRing S] (φ : R →+* S) (f : MvPolynomial (Fin r × Fin n) R) :
    swp S r n (map φ f) = map φ (swp R r n f) := by
  rw [rgl_swp_apply, rgl_swp_apply, map_rename]

theorem rgl_rowGen_X (a b : Fin r) (v : Fin r × Fin n) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  rw [rowGen, aeval_X]

theorem rgl_rowGen_C (a b : Fin r) (c : R) :
    rowGen R (n := n) a b (C c) = Polynomial.C (C c) := by
  rw [rowGen, aeval_C]; rfl

theorem rgl_rowDiv_mul (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f * g) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, rowDiv R a b ij.1 f * rowDiv R a b ij.2 g := by
  simp only [rowDiv, map_mul, Polynomial.coeff_mul]

theorem rgl_rowDiv_C_zero (a b : Fin r) (c : R) : rowDiv R (n := n) a b 0 (C c) = C c := by
  rw [rowDiv, rgl_rowGen_C, Polynomial.coeff_C_zero]

theorem rgl_rowDiv_C_succ (a b : Fin r) (k : ℕ) (c : R) : rowDiv R (n := n) a b (k + 1) (C c) = 0 := by
  rw [rowDiv, rgl_rowGen_C, Polynomial.coeff_C_succ]

theorem rgl_rowDiv_X_zero (a b : Fin r) (v : Fin r × Fin n) : rowDiv R a b 0 (X v) = X v := by
  rw [rowDiv, rgl_rowGen_X]
  split_ifs <;> simp

theorem rgl_rowDiv_X_one (a b : Fin r) (v : Fin r × Fin n) :
    rowDiv R a b 1 (X v) = if v.1 = b then X (a, v.2) else 0 := by
  rw [rowDiv, rgl_rowGen_X]
  split_ifs <;> simp

theorem rgl_rowDiv_X_two (a b : Fin r) (k : ℕ) (v : Fin r × Fin n) :
    rowDiv R a b (k + 2) (X v) = 0 := by
  rw [rowDiv, rgl_rowGen_X]
  split_ifs
  · rw [Polynomial.coeff_add, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul, Polynomial.coeff_C_succ, add_zero]
  · rw [add_zero, Polynomial.coeff_C_succ]

theorem rgl_rowDiv_zero (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) : rowDiv R a b 0 f = f := by
  induction f using MvPolynomial.induction_on with
  | C c => exact rgl_rowDiv_C_zero R a b c
  | add f g hf hg => rw [rowDiv_add, hf, hg]
  | mul_X f v hf =>
    rw [rgl_rowDiv_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hf, rgl_rowDiv_X_zero]

theorem rgl_mapDomain_apply (m : Fin r × Fin n →₀ ℕ) (a : Fin r) (s : Fin n) :
    Finsupp.mapDomain (Equiv.prodComm (Fin r) (Fin n)) m (s, a) = m (a, s) :=
  Finsupp.mapDomain_apply (Equiv.injective _) m (a, s)

theorem rgl_support_swp (f : MvPolynomial (Fin r × Fin n) R) :
    (swp R r n f).support =
      f.support.image (Finsupp.mapDomain (Equiv.prodComm (Fin r) (Fin n))) := by
  rw [rgl_swp_apply, support_rename_of_injective (Equiv.injective _)]

theorem rgl_weight_colW (m : Fin r × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (colW r n) m s = ∑ a : Fin r, m (a, s) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [colW, Pi.single_apply]

end general

variable {p : ℕ} [Fact p.Prime] {r n : ℕ}

theorem rgl_E (ν : Fin n → ℕ) (a b : Fin r) : (GR p r ν).E a b = glAct p (vecL ν) n a b := rfl

theorem rgl_glAct_X (ν : Fin n → ℕ) (a b c : Fin r) (s : Fin n) :
    glAct p (vecL ν) n a b (X (s, c)) = if c = b then X (s, a) else 0 := by
  rw [glAct_X_gen, if_pos s.isLt]
  rfl

theorem rgl_wt (ν : Fin n → ℕ) (a : Fin r) (m : Fin r × Fin n →₀ ℕ) :
    wt (vecL ν) n a (Finsupp.mapDomain (Equiv.prodComm (Fin r) (Fin n)) m) = (rowDeg m a : ℤ) := by
  unfold wt rowDeg
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [if_pos s.isLt, rgl_mapDomain_apply]
  rfl

theorem rgl_div_X (ν : Fin n → ℕ) (a b : Fin r) (hab : a ≠ b) (k : ℕ) (v : Fin r × Fin n) :
    swp ℚ_[p] r n (rowDiv ℚ_[p] a b k (X v)) =
      ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p (vecL ν) n a b) ^ k) (swp ℚ_[p] r n (X v)) := by
  obtain ⟨c, s⟩ := v
  match k with
  | 0 => simp [rgl_rowDiv_X_zero]
  | 1 =>
    rw [rgl_rowDiv_X_one, rgl_swp_X, pow_one, rgl_glAct_X]
    split_ifs <;> simp [rgl_swp_X]
  | k + 2 =>
    rw [rgl_rowDiv_X_two, pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, rgl_swp_X,
      glAct_glAct_X (vecL ν) n a b hab, map_zero, map_zero, smul_zero]

theorem gl_first_line_divided_powers : RowGlDiv := by
  intro p _ r n ν a b hab k f
  rw [rgl_E]
  induction f using MvPolynomial.induction_on generalizing k with
  | C c =>
    rw [rgl_swp_C]
    match k with
    | 0 => simp [rgl_rowDiv_C_zero, rgl_swp_C]
    | k + 1 =>
      rw [rgl_rowDiv_C_succ, pow_succ, Module.End.mul_apply, glAct_C', map_zero, map_zero, smul_zero]
  | add f g hf hg => rw [rowDiv_add, map_add, map_add, map_add, smul_add, hf, hg]
  | mul_X f v hf =>
    rw [rgl_rowDiv_mul, map_mul, divPow_mul _ (Formalism.GM.M.FB.glAct_mul (vecL ν) n a b), map_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [map_mul, hf, rgl_div_X ν a b hab]

theorem gl_one_first_line_action : RowGlOne := by
  intro p _ r n ν a b f
  rw [rgl_E]
  induction f using MvPolynomial.induction_on with
  | C c => rw [rgl_rowDiv_C_succ, rgl_swp_C, glAct_C', map_zero]
  | add f g hf hg => rw [rowDiv_add, map_add, map_add, map_add, hf, hg]
  | mul_X f v hf =>
    obtain ⟨c, s⟩ := v
    have h1 : Finset.HasAntidiagonal.antidiagonal 1 = {(0, 1), (1, 0)} := rfl
    rw [rgl_rowDiv_mul, h1, Finset.sum_pair (by decide), rgl_rowDiv_zero, rgl_rowDiv_X_zero, rgl_rowDiv_X_one,
      map_add, map_mul, map_mul, map_mul, hf, Formalism.GM.M.FB.glAct_mul, rgl_swp_X, rgl_glAct_X]
    split_ifs <;> simp [rgl_swp_X, mul_comm]

theorem swap_weight_compat : SwpWt := by
  intro p _ r n ν μ f
  classical
  unfold GR
  rw [GAe_isWt_iff, MvPolynomial.mem_restrictSupport_iff, rgl_support_swp]
  constructor
  · intro h m hm a
    have := h (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hm)) a
    rw [← rgl_wt ν a m]
    exact this
  · intro h m' hm' a
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hm')
    have := h m hm a
    rw [← rgl_wt ν a m] at this
    exact this

theorem swap_polynomial_compat : SwpPol := by
  intro p _ r n ν f hf
  classical
  rw [Pol, MvPolynomial.mem_restrictSupport_iff, rgl_support_swp]
  intro m' hm' s
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hm')
  have hw : Finsupp.weight (colW r n) m = ν := hf (mem_support_iff.mp hm)
  simp only [rgl_mapDomain_apply]
  rw [← rgl_weight_colW, hw]
  rfl

theorem swpInt_statement : SwpInt := by
  intro p _ r n f
  rw [Formalism.GM.FrozenVariableLemmas.intPol_iff]
  constructor
  · rintro ⟨F0, h⟩
    refine ⟨(swp ℤ_[p] r n).symm F0, (swp ℚ_[p] r n).injective ?_⟩
    rw [rgl_swp_map, AlgEquiv.apply_symm_apply, h]
  · rintro ⟨f0, rfl⟩
    exact ⟨swp ℤ_[p] r n f0, (rgl_swp_map _ _ f0).symm⟩

end Formalism.InvariantFactorPaths.INST
