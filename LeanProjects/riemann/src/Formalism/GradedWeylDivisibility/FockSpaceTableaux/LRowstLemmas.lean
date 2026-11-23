import Formalism.GradedWeylDivisibility.StatementA

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

section General

variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]

theorem isWH_algHom_monomial (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (m : σ →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w' (φ (monomial m c)) (Finsupp.weight w m) := by
  have hC : φ (C c) = C c := by
    rw [← MvPolynomial.algebraMap_eq]
    exact φ.commutes c
  rw [monomial_eq, map_mul, hC, Finsupp.prod, map_prod]
  simp only [map_pow]
  have h := (isWeightedHomogeneous_C w' c).mul
    (IsWeightedHomogeneous.prod m.support (fun v => φ (X v) ^ m v) (fun v => m v • w v)
      (fun v _ => (hφ v).pow (m v)))
  rw [zero_add] at h
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact h

theorem isWH_algHom (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) {f : MvPolynomial σ R} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) d := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  have h := isWH_algHom_monomial φ w w' hφ s (coeff s f)
  rwa [hf (mem_support_iff.mp hs)] at h

private theorem weightedHomogeneousComponent_self_of_isWH {w : σ → M} {p : MvPolynomial σ R} {m : M}
    (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w m p = p := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with h
  · rfl
  · by_contra hd
    exact h (hp (Ne.symm hd))

private theorem weightedHomogeneousComponent_eq_zero_of_isWH_ne {w : σ → M} {p : MvPolynomial σ R} {m μ : M}
    (hne : m ≠ μ) (hp : IsWeightedHomogeneous w p m) : weightedHomogeneousComponent w μ p = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with h
  · by_contra hd
    exact hne ((hp hd).symm.trans h)
  · rfl

theorem algHom_weightedHomogeneousComponent (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (w : σ → M) (w' : τ → M) (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (μ : M)
    (f : MvPolynomial σ R) :
    φ (weightedHomogeneousComponent w μ f) = weightedHomogeneousComponent w' μ (φ f) := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := isWH_algHom_monomial φ w w' hφ s (coeff s f)
  have hm : IsWeightedHomogeneous w (monomial s (coeff s f)) (Finsupp.weight w s) :=
    isWeightedHomogeneous_monomial w s (coeff s f) rfl
  by_cases h : Finsupp.weight w s = μ
  · subst h
    rw [weightedHomogeneousComponent_self_of_isWH hm, weightedHomogeneousComponent_self_of_isWH hs]
  · rw [weightedHomogeneousComponent_eq_zero_of_isWH_ne h hm, weightedHomogeneousComponent_eq_zero_of_isWH_ne h hs,
      map_zero]

end General

theorem rowst_mem_dualWeyl_iff {R : Type*} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule, AlgHom.toLinearMap_apply]

def rowActO (R : Type*) [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (Option (Fin r × Fin n)) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun o => Option.elim o (X none) (fun v => ∑ b : Fin r, C (g v.1 b) * X (some (b, v.2)))

theorem colAddGen_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l j (rowAct R g f) = rowActO R g (colAddGen R l j f) := by
  have key : (colAddGen R l j).comp (rowAct R g) =
      (rowActO R g).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp only [AlgHom.comp_apply, colAddGen, rowAct, rowActO, aeval_X, map_sum,
      map_mul, aeval_C, MvPolynomial.algebraMap_eq]
    by_cases h : t = j
    · simp only [h, if_true, aeval_X, map_add, map_mul, Option.elim]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    · simp [h]
  exact DFunLike.congr_fun key f

theorem rename_rowAct {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    rename (some : Fin r × Fin n → Option (Fin r × Fin n)) (rowAct R g f) =
      rowActO R g (rename some f) := by
  have key : (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).comp (rowAct R g) =
      (rowActO R g).comp (rename some) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, t⟩
    simp [rowAct, rowActO, MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun key f

theorem rowAct_X_isWH {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (v : Fin r × Fin n) : IsWeightedHomogeneous (colW r n) (rowAct R g (X v)) (colW r n v) := by
  simp only [rowAct, aeval_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
  convert (isWeightedHomogeneous_C (colW r n) (g v.1 b)).mul
    (isWeightedHomogeneous_X (R := R) (colW r n) (b, v.2)) using 1
  simp [colW]

def rowWO (r n : ℕ) : Option (Fin r × Fin n) → (Fin r → ℕ) :=
  fun o => Option.elim o 0 (fun v => Pi.single v.1 1)

end Formalism.GradedWeylDivisibility
