import Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialStableContainsComponents

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def laurentUnit (B : Type*) [CommRing B] : (LaurentPolynomial B)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

theorem laurentUnit_zpow (B : Type*) [CommRing B] (w : ℤ) :
    (((laurentUnit B) ^ w : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T w := by
  have hinv : (((laurentUnit B)⁻¹ : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T (-1) := rfl
  have hval : (((laurentUnit B) : (LaurentPolynomial B)ˣ) : LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  induction w using Int.induction_on with
  | zero => simp [LaurentPolynomial.T_zero]
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, hval, ← LaurentPolynomial.T_add]
  | pred i ih => rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add]; rfl

theorem binomialOperator_monomial {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : R) :
    binomPol R LL S a k (monomial m c) = monomial m (c * ((Ring.choose (wtS LL S m a) k : ℤ) : R)) := by
  have hm : (monomial m c : MvPolynomial (ι × Fin n) R) = c • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, LinearMap.map_smul]
  simp only [binomPol]
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι) (j : Fin n)
  (Pr : ℤ → Prop)

def weightEntryPropertySubmodule : Submodule R (MvPolynomial (ι × Fin n) R) where
  carrier := {y | ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1),
    g0 * g0inv = 1 → ∀ m ∈ (matrixSubst LL S φ g0inv g0 y).support, Pr (wtS LL S m j)}
  zero_mem' := by
    intro k1 _ φ g0 g0inv _ m hm
    simp at hm
  add_mem' := by
    classical
    intro x y hx hy k1 _ φ g0 g0inv h m hm
    rw [map_add] at hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
    · exact hx k1 φ g0 g0inv h m h1
    · exact hy k1 φ g0 g0inv h m h1
  smul_mem' := by
    intro c y hy k1 _ φ g0 g0inv h m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
    exact hy k1 φ g0 g0inv h m (MvPolynomial.support_smul hm)

theorem laurent_coefficients_mem_property (y : MvPolynomial (ι × Fin n) R) (K : Finset ℤ) (yk : ℤ → MvPolynomial (ι × Fin n) R)
    (hh : ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1), ∃ h h' : Matrix (Fin n) (Fin n) (LaurentPolynomial k1),
      h' * h = 1 ∧ matrixSubst LL S (LaurentPolynomial.C.comp φ) h h' y =
        ∑ k ∈ K, C (LaurentPolynomial.T k) * MvPolynomial.map (LaurentPolynomial.C.comp φ) (yk k))
    (hy : y ∈ weightEntryPropertySubmodule LL S j Pr) : ∀ k ∈ K, yk k ∈ weightEntryPropertySubmodule LL S j Pr := by
  classical
  intro k hk k1 _ φ g0 g0inv hg m hm
  obtain ⟨h, h', hh1, hE⟩ := hh k1 φ
  set ψ : k1 →+* LaurentPolynomial k1 := LaurentPolynomial.C with hψ
  have h2 : g0.map ψ * g0inv.map ψ = 1 := by
    rw [← Matrix.map_mul, hg, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
  have hinv : (h' * g0.map ψ) * (g0inv.map ψ * h) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (g0.map ψ), h2, Matrix.one_mul, hh1]
  apply hy (LaurentPolynomial k1) (ψ.comp φ) (h' * g0.map ψ) (g0inv.map ψ * h) hinv m
  rw [← matrixSubst_comp, hE, map_sum]
  have hA : ∀ k', matrixSubst LL S (RingHom.id _) (g0inv.map ψ) (g0.map ψ)
      (C (LaurentPolynomial.T k') * MvPolynomial.map (ψ.comp φ) (yk k')) =
      C (LaurentPolynomial.T k') * MvPolynomial.map ψ (matrixSubst LL S φ g0inv g0 (yk k')) := by
    intro k'
    rw [map_mul, matrixSubst_C, RingHom.id_apply, matrixSubst_map, map_matrixSubst]
  simp_rw [hA]
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  intro hz
  apply hm
  rw [MvPolynomial.coeff_sum] at hz
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hz
  have hz2 := congrArg (fun p : LaurentPolynomial k1 => p.coeff k) hz
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at hz2
  have hT : ∀ k' (c : k1), (LaurentPolynomial.T k' * ψ c).coeff k = if k' = k then c else 0 := by
    intro k' c
    rw [hψ, mul_comm, ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp_rw [hT, Finset.sum_ite_eq' K k] at hz2
  simpa [hk] using hz2

end fwd

end Formalism.MainNotions.G.GLWeightTheory
