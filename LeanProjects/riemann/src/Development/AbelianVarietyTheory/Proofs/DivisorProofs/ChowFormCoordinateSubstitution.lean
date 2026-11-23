import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChowIncl

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

variable {K : Type} [Field K] {N n : ℕ}

theorem isChowFormInt_linSubst_of_irreducible {M : Matrix (Fin N) (Fin n) K} {P : Matrix (Fin n) (Fin N) K}
    (h : M * P = 1) {I : Ideal (MvPolynomial (Fin N) K)} {I' : Ideal (MvPolynomial (Fin n) K)}
    (hI : ∀ g, g ∈ I' ↔ coordSubst M g ∈ I) {D δ : ℕ} {f : MvPolynomial (Fin (D + 1) × Fin N) K}
    (hf : IsChowFormInt I D δ f) (hirr : Irreducible (linSubst M f)) : IsChowFormInt I' D δ (linSubst M f) := by
  refine ⟨HeightUnique.linSubst_homog M hf.homog, hirr, fun u => ?_⟩
  have e : aeval u (linSubst M f) =
      aeval (fun p : Fin (D + 1) × Fin N => ∑ k, algebraMap K _ (M p.2 k) * u (p.1, k)) f := by
    rw [linSubst, ← AlgHom.comp_apply]
    congr 1
    exact MvPolynomial.algHom_ext fun k => by simp
  have pair : ∀ (y : Fin N → AlgebraicClosure K) (i : Fin (D + 1)),
      ∑ j, (∑ k, algebraMap K _ (M j k) * u (i, k)) * y j = ∑ k, u (i, k) * ∑ j, algebraMap K _ (M j k) * y j :=
    fun y i => by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e, hf.zero_iff]
  constructor
  · rintro ⟨y, hy, h1, h2⟩
    refine ⟨fun k => ∑ j, algebraMap K _ (M j k) * y j, fun h0 => hy (funext fun j => ?_), fun g hg => ?_,
      fun i => (pair y i).symm.trans (h2 i)⟩
    · rw [← sum_sum_eq h y j]
      exact Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ (congrFun h0 k)
    · rw [← aeval_coordSubst]; exact h1 _ ((hI g).1 hg)
  · rintro ⟨y, hy, h1, h2⟩
    have back : ∀ k, ∑ j, algebraMap K _ (M j k) * ∑ i, algebraMap K _ (P i j) * y i = y k := fun k => by
      have hm : X k - coordSubst P (coordSubst M (X k)) ∈ I' :=
        (hI _).2 (by rw [map_sub, coordSubst_coordSubst h, sub_self]; exact I.zero_mem)
      have := h1 _ hm
      rw [map_sub, aeval_coordSubst, aeval_coordSubst, aeval_X, aeval_X, sub_eq_zero] at this
      exact this.symm
    refine ⟨fun j => ∑ k, algebraMap K _ (P k j) * y k, fun h0 => hy (funext fun k => ?_), fun g hg => ?_,
      fun i => (pair _ i).trans ?_⟩
    · rw [← back k]
      exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_right _ (congrFun h0 j)
    · rw [← aeval_coordSubst]
      exact h1 _ ((hI _).2 (by rwa [coordSubst_coordSubst h]))
    · simp only [back]; exact h2 i

theorem linSubst_incl_eq_rename {B : ℕ} (h : N ≤ n) (f : MvPolynomial (Fin B × Fin N) K) :
    linSubst (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) f =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f := by
  unfold GlobalTheory.ChowHt.linSubst
  have hfun : (fun p : Fin B × Fin N => ∑ k : Fin n, C ((Matrix.of fun (j : Fin N) (k : Fin n) =>
      if (j : ℕ) = (k : ℕ) then (1 : K) else 0) p.2 k) * X (p.1, k)) =
      fun p => X (p.1, Fin.castLE h p.2) := by
    funext p
    rw [Fintype.sum_eq_single (Fin.castLE h p.2)]
    · simp
    · intro k hk
      have hne : (p.2 : ℕ) ≠ (k : ℕ) := fun he => hk (Fin.ext he.symm)
      simp [Matrix.of_apply, hne]
  rw [hfun]
  have hal : (aeval fun p : Fin B × Fin N => (X (p.1, Fin.castLE h p.2) : MvPolynomial (Fin B × Fin n) K)) =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) :=
    MvPolynomial.algHom_ext fun p => by simp
  rw [hal]

theorem irreducible_rename_of_injective {σ τ : Type} {e : σ → τ} (he : Function.Injective e)
    {f : MvPolynomial σ K} (hf : Irreducible f) : Irreducible (rename e f) := by
  classical
  have hp : Prime f := hf.prime
  let e' := Equiv.ofInjective _ he
  have h1 : Prime (rename e' f) := (MulEquiv.prime_iff (renameEquiv K e').toMulEquiv).2 hp
  have h2 : Prime (rename ((↑) : Set.range e → τ) (rename e' f)) := (prime_rename_iff _).2 h1
  rw [rename_rename] at h2
  have h3 : ((↑) : Set.range e → τ) ∘ e' = e := by
    funext p; simp [e']
  rw [h3] at h2
  exact h2.irreducible

theorem incl_mul_transpose (h : N ≤ n) :
    (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) *
      (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0).transpose = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.castLE h i)]
  · simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
  · intro k hk
    have hne : (i : ℕ) ≠ (k : ℕ) := fun he => hk (Fin.ext he.symm)
    simp [hne]

theorem isChowFormInt_incl (K : Type) [Field K] (N n D δ : ℕ) (I : Ideal (MvPolynomial (Fin N) K))
    (I' : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (D + 1) × Fin N) K) (h : N ≤ n)
    (hI : ∀ q, q ∈ I' ↔ coordSubst
      (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) q ∈ I)
    (hf : IsChowFormInt I D δ f) :
    IsChowFormInt I' D δ
      (linSubst (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) f) := by
  refine isChowFormInt_linSubst_of_irreducible (incl_mul_transpose h) hI hf ?_
  rw [linSubst_incl_eq_rename h]
  refine irreducible_rename_of_injective (fun p q hpq => ?_) hf.irred
  simp only [Prod.mk.injEq] at hpq
  exact Prod.ext hpq.1 (Fin.castLE_injective h hpq.2)

end GlobalTheory.ChowIncl
