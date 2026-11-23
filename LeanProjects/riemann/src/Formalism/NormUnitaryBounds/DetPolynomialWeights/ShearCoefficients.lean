import Formalism.NormUnitaryBounds.Statement

open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

namespace ShearCoefficients

variable {R : Type*} [CommRing R]

lemma mem_H_iff {N n : ℕ} (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R) :
    F ∈ H R ν ↔ F.IsWeightedHomogeneous (blockWt N n) ν ∧
      ∀ i j : Fin N, i < j → shear R i j F = Polynomial.C F := by
  simp only [H, Submodule.mem_inf, mem_weightedHomogeneousSubmodule, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    IsScalarTower.toAlgHom_apply, sub_eq_zero]
  rfl

lemma weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (f : σ → τ)
    (d : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f d) = Finsupp.weight (w ∘ f) d := by
  classical
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]

lemma isWeightedHomogeneous_rename {σ τ M : Type*} [AddCommMonoid M] {w : τ → M} {f : σ → τ}
    {m : M} {F : MvPolynomial σ R} (hF : F.IsWeightedHomogeneous (w ∘ f) m) :
    (rename f F).IsWeightedHomogeneous w m := by
  refine IsWeightedHomogeneous.induction_on
    (motive := fun p _ => (rename f p).IsWeightedHomogeneous w m) ?_ ?_ ?_ hF
  · simpa using isWeightedHomogeneous_zero R w m
  · intro p q _ _ hp hq
    rw [map_add]; exact hp.add hq
  · intro d r hr
    rw [rename_monomial]
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [weight_mapDomain, hr])

lemma shear_rename_perm {N n : ℕ} (i j : Fin N) (σ : Equiv.Perm (Fin n))
    (F : MvPolynomial (Fin N × Fin n) R) :
    shear R i j (rename (fun p : Fin N × Fin n => (p.1, σ p.2)) F) =
      Polynomial.map (rename (R := R) (fun p : Fin N × Fin n => (p.1, σ p.2))).toRingHom
        (shear R i j F) := by
  have key : (shear R i j).comp (rename (fun p : Fin N × Fin n => (p.1, σ p.2))) =
      (Polynomial.mapAlgHom (rename (fun p : Fin N × Fin n => (p.1, σ p.2)))).comp
        (shear R i j) := by
    apply MvPolynomial.algHom_ext
    intro p
    by_cases h : p.1 = j <;> simp [shear, h]
  have h := congrArg (fun φ => φ F) key
  simpa [Polynomial.coe_mapAlgHom] using h

theorem perm : NormUnitaryPermutationInvariance := by
  intro R _ N n ν σ F hF
  rw [mem_H_iff] at hF ⊢
  refine ⟨isWeightedHomogeneous_rename hF.1, fun i j hij => ?_⟩
  rw [shear_rename_perm, hF.2 i j hij, Polynomial.map_C]
  rfl

def CoeffHom {σ M : Type*} [AddCommMonoid M] (wt : σ → M) (m : M)
    (P : Polynomial (MvPolynomial σ R)) : Prop :=
  ∀ k, (P.coeff k).IsWeightedHomogeneous wt m

section CoeffHom

variable {σ M : Type*} [AddCommMonoid M] {wt : σ → M}

lemma CoeffHom.add {m : M} {P Q : Polynomial (MvPolynomial σ R)} (hP : CoeffHom wt m P)
    (hQ : CoeffHom wt m Q) : CoeffHom wt m (P + Q) := by
  intro k; rw [Polynomial.coeff_add]; exact (hP k).add (hQ k)

lemma CoeffHom.zero (m : M) : CoeffHom (R := R) wt m 0 := by
  intro k; rw [Polynomial.coeff_zero]; exact isWeightedHomogeneous_zero R wt m

lemma CoeffHom.mul {a b : M} {P Q : Polynomial (MvPolynomial σ R)} (hP : CoeffHom wt a P)
    (hQ : CoeffHom wt b Q) : CoeffHom wt (a + b) (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact IsWeightedHomogeneous.sum _ _ _ (fun x _ => (hP x.1).mul (hQ x.2))

lemma CoeffHom.C {m : M} {r : MvPolynomial σ R} (h : r.IsWeightedHomogeneous wt m) :
    CoeffHom wt m (Polynomial.C r) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact h
  · exact isWeightedHomogeneous_zero R wt m

lemma CoeffHom.X : CoeffHom (R := R) wt 0 Polynomial.X := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs
  · exact isWeightedHomogeneous_one R wt
  · exact isWeightedHomogeneous_zero R wt 0

lemma CoeffHom.one : CoeffHom (R := R) wt 0 1 := by
  simpa using CoeffHom.C (R := R) (isWeightedHomogeneous_one R wt)

lemma CoeffHom.pow {a : M} {P : Polynomial (MvPolynomial σ R)} (h : CoeffHom wt a P) (e : ℕ) :
    CoeffHom wt (e • a) (P ^ e) := by
  induction e with
  | zero => simpa using CoeffHom.one (R := R) (wt := wt)
  | succ e ih => rw [pow_succ, succ_nsmul]; exact ih.mul h

lemma CoeffHom.prod {ι : Type*} (s : Finset ι) (P : ι → Polynomial (MvPolynomial σ R))
    (a : ι → M) (h : ∀ x ∈ s, CoeffHom wt (a x) (P x)) :
    CoeffHom wt (∑ x ∈ s, a x) (∏ x ∈ s, P x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffHom.one (R := R) (wt := wt)
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).mul
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

end CoeffHom

lemma coeffHom_shear_X {N n : ℕ} (i j : Fin N) (p : Fin N × Fin n) :
    CoeffHom (R := R) (coordWt N n) (coordWt N n p)
      (Polynomial.C (X p) +
        (if p.1 = j then Polynomial.X * Polynomial.C (X (i, p.2)) else 0)) := by
  refine CoeffHom.add (CoeffHom.C (isWeightedHomogeneous_X R _ p)) ?_
  split_ifs
  · have h := (CoeffHom.X (R := R) (wt := coordWt N n)).mul
      (CoeffHom.C (isWeightedHomogeneous_X R (coordWt N n) (i, p.2)))
    rw [zero_add] at h
    exact h
  · exact CoeffHom.zero _

lemma coeffHom_shear_monomial {N n : ℕ} (i j : Fin N) (d : (Fin N × Fin n) →₀ ℕ) (r : R) :
    CoeffHom (coordWt N n) (Finsupp.weight (coordWt N n) d) (shear R i j (monomial d r)) := by
  rw [shear, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
    ← zero_add (∑ a ∈ d.support, d a • coordWt N n a)]
  refine CoeffHom.mul ?_ (CoeffHom.prod _ _ _ fun p _ => (coeffHom_shear_X i j p).pow _)
  rw [Polynomial.algebraMap_apply]
  exact CoeffHom.C (isWeightedHomogeneous_C _ _)

lemma comp_coeff_shear {N n : ℕ} (i j : Fin N) (w : Fin n → ℕ)
    (F : MvPolynomial (Fin N × Fin n) R) (k : ℕ) :
    weightedHomogeneousComponent (coordWt N n) w ((shear R i j F).coeff k) =
      (shear R i j (weightedHomogeneousComponent (coordWt N n) w F)).coeff k := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [weightedHomogeneousComponent_of_mem (coeffHom_shear_monomial i j d r k),
      weightedHomogeneousComponent_of_mem
        (isWeightedHomogeneous_monomial (coordWt N n) d r rfl)]
    split_ifs <;> simp
  | add p q hp hq =>
    rw [map_add, map_add, Polynomial.coeff_add, map_add, hp, hq, map_add, Polynomial.coeff_add]

theorem weight : NormUnitaryWeight := by
  classical
  intro R _ N n ν F hF w
  rw [mem_H_iff] at hF ⊢
  refine ⟨?_, fun i j hij => ?_⟩
  · intro d hd
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd
    · exact hF.1 hd
    · exact absurd rfl hd
  · refine Polynomial.ext fun k => ?_
    rw [← comp_coeff_shear, hF.2 i j hij, Polynomial.coeff_C, Polynomial.coeff_C]
    split_ifs <;> simp

end ShearCoefficients

end Formalism.NormUnitaryCountingLemmas
