import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA

open MvPolynomial

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} [Fintype ι]
  {K : Type*} [CommSemiring K] (σ : K →+* ℂ)

theorem hasFDerivAt_mv (q : MvPolynomial ι K) {h : V → ι → ℂ} {z0 : V} {Dh : ι → V →L[ℂ] ℂ}
    (hh : ∀ i, HasFDerivAt (fun z => h z i) (Dh i) z0) :
    HasFDerivAt (fun z => eval₂ σ (h z) q) (∑ i, eval₂ σ (h z0) (pderiv i q) • Dh i) z0 := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const (σ a) z0
  | add p q hp hq =>
    simp only [eval₂_add, map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X]
    refine (hp.mul (hh i)).congr_fderiv ?_
    simp only [Derivation.leibniz, smul_eq_mul, eval₂_add, eval₂_mul, eval₂_X, add_smul,
      Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp [pderiv_X_self]
    · intro b _ hb
      classical
      rw [pderiv_X]
      simp [hb.symm]
    · simp

def xTerm {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (P : Polynomial (MvPolynomial ι K)) : R :=
  P.sum fun n c => ψ (pderiv i c) * s ^ n

theorem xTerm_add {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (P Q : Polynomial (MvPolynomial ι K)) : xTerm ψ s i (P + Q) = xTerm ψ s i P + xTerm ψ s i Q := by
  unfold xTerm
  exact Polynomial.sum_add_index _ _ _ (by simp) (by intros; simp [add_mul])

theorem xTerm_monomial {R : Type*} [CommSemiring R] (ψ : MvPolynomial ι K →+* R) (s : R) (i : ι)
    (n : ℕ) (c : MvPolynomial ι K) : xTerm ψ s i (Polynomial.monomial n c) = ψ (pderiv i c) * s ^ n := by
  unfold xTerm
  exact Polynomial.sum_monomial_index _ _ (by simp)

theorem map_xTerm {R S : Type*} [CommSemiring R] [CommSemiring S] (ψ : MvPolynomial ι K →+* R)
    (f : R →+* S) (s : R) (i : ι) (P : Polynomial (MvPolynomial ι K)) :
    f (xTerm ψ s i P) = xTerm (f.comp ψ) (f s) i P := by
  unfold xTerm Polynomial.sum
  simp [map_sum]

theorem hasFDerivAt_eval₂ (P : Polynomial (MvPolynomial ι K)) {h : V → ι → ℂ} {g : V → ℂ} {z0 : V}
    {Dh : ι → V →L[ℂ] ℂ} {Dg : V →L[ℂ] ℂ}
    (hh : ∀ i, HasFDerivAt (fun z => h z i) (Dh i) z0) (hg : HasFDerivAt g Dg z0) :
    HasFDerivAt (fun z => P.eval₂ (eval₂Hom σ (h z)) (g z))
      ((Polynomial.derivative P).eval₂ (eval₂Hom σ (h z0)) (g z0) • Dg +
        ∑ i, xTerm (eval₂Hom σ (h z0)) (g z0) i P • Dh i) z0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval₂_add]
    refine (hp.add hq).congr_fderiv ?_
    simp only [map_add, Polynomial.eval₂_add, xTerm_add, add_smul, Finset.sum_add_distrib]
    abel
  | monomial n c =>
    simp only [Polynomial.eval₂_monomial]
    refine ((hasFDerivAt_mv σ c hh).mul (hg.pow n)).congr_fderiv ?_
    simp only [Polynomial.derivative_monomial, xTerm_monomial, Polynomial.eval₂_monomial, coe_eval₂Hom,
      Finset.smul_sum, smul_smul, map_mul, map_natCast, nsmul_eq_mul]
    congr 1
    · congr 1; ring
    · exact Finset.sum_congr rfl fun b _ => by rw [mul_comm]

omit [Fintype ι] in

theorem exists_rel {K Ω : Type*} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {y : ι → Ω}
    (hy : AlgebraicIndependent K y) {a : Ω} (ha : IsAlgebraic (Algebra.adjoin K (Set.range y)) a) :
    ∃ P : Polynomial (MvPolynomial ι K), P.eval₂ (aeval y).toRingHom a = 0 ∧
      (Polynomial.derivative P).eval₂ (aeval y).toRingHom a ≠ 0 := by
  classical
  obtain ⟨q, hq0, hqa⟩ := ha
  let f : Algebra.adjoin K (Set.range y) →+* MvPolynomial ι K := hy.aevalEquiv.symm.toRingHom
  have hf : Function.Injective f := hy.aevalEquiv.symm.injective
  have hcomp : (aeval y).toRingHom.comp f = algebraMap (Algebra.adjoin K (Set.range y)) Ω := by
    ext s
    have := hy.algebraMap_aevalEquiv (hy.aevalEquiv.symm s)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  have hex : ∃ n, ∃ P : Polynomial (MvPolynomial ι K), P ≠ 0 ∧
      P.eval₂ (aeval y).toRingHom a = 0 ∧ P.natDegree = n := by
    refine ⟨_, q.map f, (Polynomial.map_ne_zero_iff hf).mpr hq0, ?_, rfl⟩
    rw [Polynomial.eval₂_map, hcomp]
    exact hqa
  obtain ⟨P, hP0, hPa, hPn⟩ := Nat.find_spec hex
  refine ⟨P, hPa, fun hd => ?_⟩
  by_cases hD : Polynomial.derivative P = 0
  · have h0 : P.natDegree = 0 := Polynomial.derivative_eq_zero.mp hD
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, Polynomial.eval₂_C] at hPa
    have hc : P.coeff 0 = 0 := hy (by simpa using hPa)
    apply hP0
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero]
  · have hne : P.natDegree ≠ 0 := fun h0 => hD (Polynomial.derivative_eq_zero.mpr h0)
    have hlt := Polynomial.natDegree_derivative_lt hne
    rw [hPn] at hlt
    exact Nat.find_min hex hlt ⟨_, hD, hd, rfl⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA
