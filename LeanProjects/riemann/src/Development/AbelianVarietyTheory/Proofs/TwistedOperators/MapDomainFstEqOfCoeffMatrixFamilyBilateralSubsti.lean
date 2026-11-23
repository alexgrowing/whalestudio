import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem weight_fst_eq_mapDomain {ι κ : Type} (k : ι × κ →₀ ℕ) :
    Finsupp.weight (fun p : ι × κ => (Finsupp.single p.1 1 : ι →₀ ℕ)) k = Finsupp.mapDomain Prod.fst k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain]
  refine Finsupp.sum_congr fun p _ => ?_
  simp

theorem substF_X_isWeightedHomogeneous {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (X p)) (Finsupp.single p.1 1) := by
  rw [substF_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun k _ => IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
  have h1 := isWeightedHomogeneous_X ℂ (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ)) (p.1, k, l)
  have h2 := (isWeightedHomogeneous_C (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
    (h p.1 k p.2.1 * g p.1 l p.2.2)).mul h1
  rwa [zero_add] at h2

theorem mapDomain_fst_eq_of_coeff_substF_ne_zero {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ)
    (hk : MvPolynomial.coeff k' (substF h g (MvPolynomial.monomial k 1)) ≠ 0) :
    Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  have key : IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (MvPolynomial.monomial k 1)) (Finsupp.mapDomain Prod.fst k) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, ← weight_fst_eq_mapDomain, Finsupp.weight_apply,
      Finsupp.sum]
    refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
    rw [map_pow]
    exact (substF_X_isWeightedHomogeneous h g p).pow (k p)
  rw [← weight_fst_eq_mapDomain]
  exact key hk

end GlobalTheory.CompactHowe

end
