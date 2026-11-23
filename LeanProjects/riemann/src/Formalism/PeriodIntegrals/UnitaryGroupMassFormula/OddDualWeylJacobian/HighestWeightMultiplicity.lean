import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace Hom

variable {R : Type} [CommRing R] {k : ℕ}

def Good (wt : Fin k × Fin k → ℤ) (δ d : ℤ) (p : Polynomial (MvPolynomial (Fin k × Fin k) R)) :
    Prop :=
  ∀ i : ℕ, IsWeightedHomogeneous wt (p.coeff i) (d + i * δ)

variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}

theorem good_congr {d e : ℤ} {p : Polynomial (MvPolynomial (Fin k × Fin k) R)} (h : d = e)
    (hp : Good wt δ d p) : Good wt δ e p := by
  subst h
  exact hp

theorem good_zero (d : ℤ) : Good (R := R) wt δ d 0 := by
  intro i e he
  simp at he

theorem good_add {d : ℤ} {p q : Polynomial (MvPolynomial (Fin k × Fin k) R)}
    (hp : Good wt δ d p) (hq : Good wt δ d q) : Good wt δ d (p + q) := by
  intro i
  rw [Polynomial.coeff_add]
  exact (hp i).add (hq i)

theorem good_C {d : ℤ} {c : MvPolynomial (Fin k × Fin k) R} (hc : IsWeightedHomogeneous wt c d) :
    Good wt δ d (Polynomial.C c) := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simpa using hc
  · intro e he
    simp at he

theorem good_X_mul_C {d : ℤ} {c : MvPolynomial (Fin k × Fin k) R}
    (hc : IsWeightedHomogeneous wt c (d + δ)) : Good wt δ d (Polynomial.X * Polynomial.C c) := by
  intro i
  rw [Polynomial.X_mul_C, Polynomial.coeff_C_mul_X]
  split_ifs with h
  · subst h
    simpa using hc
  · intro e he
    simp at he

theorem good_one : Good (R := R) wt δ 0 1 := by
  simpa using good_C (δ := δ) (isWeightedHomogeneous_one (R := R) (w := wt))

theorem good_mul {d e : ℤ} {p q : Polynomial (MvPolynomial (Fin k × Fin k) R)}
    (hp : Good wt δ d p) (hq : Good wt δ e q) : Good wt δ (d + e) (p * q) := by
  intro i
  rw [Polynomial.coeff_mul, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [mem_weightedHomogeneousSubmodule]
  have h := (hp x.1).mul (hq x.2)
  convert h using 1
  rw [← hx]
  push_cast
  ring

theorem good_pow {d : ℤ} {p : Polynomial (MvPolynomial (Fin k × Fin k) R)} (hp : Good wt δ d p)
    (m : ℕ) : Good wt δ (m * d) (p ^ m) := by
  induction m with
  | zero => simpa using (good_one (R := R) (wt := wt) (δ := δ))
  | succ m ih =>
    rw [pow_succ]
    exact good_congr (by push_cast; ring) (good_mul ih hp)

theorem good_prod {ι : Type*} (s : Finset ι) (p : ι → Polynomial (MvPolynomial (Fin k × Fin k) R))
    (d : ι → ℤ) (h : ∀ i ∈ s, Good wt δ (d i) (p i)) : Good wt δ (∑ i ∈ s, d i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on
  · simpa using (good_one (R := R) (wt := wt) (δ := δ))
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact good_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem good_rowGen_X (a b : Fin k) (hδ : ∀ s, wt (a, s) = wt (b, s) + δ) (v : Fin k × Fin k) :
    Good wt δ (wt v) (rowGen R a b (X v)) := by
  simp only [rowGen, aeval_X]
  refine good_add (good_C (isWeightedHomogeneous_X R wt v)) ?_
  split_ifs with h
  · apply good_X_mul_C
    obtain ⟨v1, v2⟩ := v
    simp only at h ⊢
    subst h
    rw [← hδ]
    exact isWeightedHomogeneous_X R wt (a, v2)
  · exact good_zero _

theorem good_rowGen (a b : Fin k) (hδ : ∀ s, wt (a, s) = wt (b, s) + δ) {d : ℤ}
    {f : MvPolynomial (Fin k × Fin k) R} (hf : IsWeightedHomogeneous wt f d) :
    Good wt δ d (rowGen R a b f) := by
  have key : ∀ m ∈ f.support, Good wt δ d (rowGen R a b (monomial m (coeff m f))) := by
    intro m hm
    have hw : Finsupp.weight wt m = d := hf (mem_support_iff.mp hm)
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    have h1 : Good wt δ 0 (rowGen R a b (C (coeff m f))) := by
      have hC : rowGen R a b (C (coeff m f) : MvPolynomial (Fin k × Fin k) R) = Polynomial.C (C (coeff m f) : MvPolynomial (Fin k × Fin k) R) := by
        simp [rowGen, Polynomial.algebraMap_apply]
      rw [hC]
      exact good_C (isWeightedHomogeneous_C wt _)
    have h2 := good_prod m.support (fun i => rowGen R a b (X i ^ m i)) (fun i => (m i : ℤ) * wt i)
      (fun i _ => by rw [map_pow]; exact good_pow (good_rowGen_X a b hδ i) (m i))
    refine good_congr ?_ (good_mul h1 h2)
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    simp [nsmul_eq_mul]
  rw [f.as_sum, map_sum]
  intro i
  rw [Polynomial.finset_sum_coeff, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_weightedHomogeneousSubmodule]
  exact key m hm i

theorem weight_cast (w : Fin k × Fin k → ℕ) (α : Fin k × Fin k →₀ ℕ) :
    Finsupp.weight (fun v => (w v : ℤ)) α = (Finsupp.weight w α : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]

theorem toZ {w : Fin k × Fin k → ℕ} {f : MvPolynomial (Fin k × Fin k) R} {d : ℕ}
    (h : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous (fun v => (w v : ℤ)) f (d : ℤ) := by
  intro α hα
  rw [weight_cast, h hα]

theorem ofZ {w : Fin k × Fin k → ℕ} {f : MvPolynomial (Fin k × Fin k) R} {m : ℤ}
    (h : IsWeightedHomogeneous (fun v => (w v : ℤ)) f m) : IsWeightedHomogeneous w f m.toNat := by
  intro α hα
  have := h hα
  rw [weight_cast] at this
  omega

theorem det_isWH {M' : Type*} [AddCommMonoid M'] {w : Fin k × Fin k → M'} {s : ℕ}
    (N : Matrix (Fin s) (Fin s) (MvPolynomial (Fin k × Fin k) R)) (r : Fin s → M')
    (h : ∀ p q, IsWeightedHomogeneous w (N p q) (r p)) :
    IsWeightedHomogeneous w N.det (∑ p, r p) := by
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hprod : (∏ i, N (σ i) i) ∈ weightedHomogeneousSubmodule R w (∑ p, r p) := by
    rw [mem_weightedHomogeneousSubmodule]
    have := IsWeightedHomogeneous.prod Finset.univ (fun i => N (σ i) i) (fun i => r (σ i))
      (fun i _ => h (σ i) i)
    rwa [Equiv.sum_comp σ r] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rw [Units.neg_smul, one_smul]
    exact Submodule.neg_mem _ hprod

theorem lpMinor_row (s : ℕ) (hr : s ≤ k) (hn : s ≤ k) (c : Fin k) :
    IsWeightedHomogeneous (rowW c) (lpMinor R s hr hn)
      (∑ p : Fin s, if Fin.castLE hr p = c then 1 else 0) := by
  unfold lpMinor
  apply det_isWH
  intro p q
  simp only [Matrix.of_apply]
  convert isWeightedHomogeneous_X R (rowW c) (Fin.castLE hr p, Fin.castLE hn q) using 1
  simp [rowW]

theorem lpMinor_tot (s : ℕ) (hr : s ≤ k) (hn : s ≤ k) :
    IsWeightedHomogeneous (1 : Fin k × Fin k → ℕ) (lpMinor R s hr hn) s := by
  have := det_isWH (w := (1 : Fin k × Fin k → ℕ))
    (Matrix.of fun p q : Fin s => (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin k × Fin k) R))
    (fun _ => 1)
    (fun p q => by simpa using isWeightedHomogeneous_X R (1 : Fin k × Fin k → ℕ) (Fin.castLE hr p, Fin.castLE hn q))
  simpa [lpMinor] using this

theorem rowDiv_tot (a b : Fin k) (j : ℕ) {f : MvPolynomial (Fin k × Fin k) R} {n : ℕ}
    (hf : IsHomogeneous f n) : IsHomogeneous (rowDiv R a b j f) n := by
  have h := good_rowGen (wt := fun v => (((1 : Fin k × Fin k → ℕ) v : ℕ) : ℤ)) (δ := 0) a b
    (fun s => by simp) (toZ (w := 1) hf) j
  have h2 := ofZ (w := 1) h
  have h3 : ((n : ℤ) + (j : ℤ) * 0).toNat = n := by simp
  rw [h3] at h2
  exact h2

theorem applyWord_tot (wd : List (Fin k × Fin k × ℕ)) {f : MvPolynomial (Fin k × Fin k) R} {n : ℕ}
    (hf : IsHomogeneous f n) : IsHomogeneous (applyWord R wd f) n := by
  induction wd with
  | nil => exact hf
  | cons x w ih => exact rowDiv_tot x.1 x.2.1 x.2.2 ih

theorem hw_tot (ν : Fin k → ℕ) : IsHomogeneous (hw R (le_refl k) ν) (degW ν) := by
  unfold hw degW
  apply IsHomogeneous.prod
  intro s _
  have h0 : IsHomogeneous (lpMinor R (s.val + 1) (by omega) (by omega) : MvPolynomial (Fin k × Fin k) R)
      (s.val + 1) := lpMinor_tot _ _ _
  convert h0.pow (ν s - nuNext ν s) using 1 <;> exact Nat.mul_comm _ _

theorem rowGen_diag_X (a : Fin k) (v : Fin k × Fin k) :
    rowGen R a a (X v) = (1 + Polynomial.X) ^ (rowW a v) * Polynomial.C (X v) := by
  simp only [rowGen, aeval_X, rowW]
  split_ifs with h
  · obtain ⟨v1, v2⟩ := v
    simp only at h ⊢
    subst h
    ring
  · simp

theorem rowGen_diag (a : Fin k) {d : ℕ} {f : MvPolynomial (Fin k × Fin k) R}
    (hf : IsWeightedHomogeneous (rowW a) f d) :
    rowGen R a a f = (1 + Polynomial.X) ^ d * Polynomial.C f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (rowW a) m = d := hf (mem_support_iff.mp hm)
  have hC : rowGen R a a (C (coeff m f) : MvPolynomial (Fin k × Fin k) R) = Polynomial.C (C (coeff m f) : MvPolynomial (Fin k × Fin k) R) := by
    simp [rowGen, Polynomial.algebraMap_apply]
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, map_mul, map_prod, hC]
  simp_rw [map_pow, rowGen_diag_X, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  simp only [smul_eq_mul, mul_comm (m _) (rowW a _)]
  ring

end Hom

open Hom

theorem highest_weight_multiplicity : MHhw := by
  intro R _ k ν a
  unfold hw
  exact ⟨_, IsWeightedHomogeneous.prod _ _ _ (fun s _ => (lpMinor_row (R := R) (s.val + 1) _ _ a).pow _)⟩

theorem highest_weight_divisibility : MHdiv := by
  intro R _ k a b j f hf c
  obtain ⟨d, hd⟩ := hf c
  refine ⟨_, ofZ (good_rowGen (wt := fun v => ((rowW c v : ℕ) : ℤ))
    (δ := ((if a = c then 1 else 0 : ℕ) : ℤ) - ((if b = c then 1 else 0 : ℕ) : ℤ)) a b ?_ (toZ hd) j)⟩
  intro s
  simp only [rowW]
  split_ifs <;> simp

theorem hermitianDiagonalization : Diag := by
  intro R _ k a j d f hf
  unfold rowDiv
  rw [rowGen_diag a hf, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow]

theorem weight_homomorphism : HomW := by
  intro R _ k ν f hf
  have hle : weyl R k k (le_refl k) ν ≤ homogeneousSubmodule (Fin k × Fin k) R (degW ν) := by
    rw [weyl, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    exact applyWord_tot w (hw_tot ν)
  have := hle hf
  rwa [mem_homogeneousSubmodule] at this

end PI.OddDualWeyl
