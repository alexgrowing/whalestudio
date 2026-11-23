import Mathlib

open Polynomial

namespace GlobalTheory.NormFormBound

theorem prod_pow_bound {k σ : Type} [Field k] (s : Finset σ) (m : σ → ℕ) (p : σ → k[X]) (d : ℕ)
    (hp : ∀ i, (p i).natDegree ≤ d) :
    (∏ i ∈ s, p i ^ m i).natDegree ≤ (∑ i ∈ s, m i) * d ∧
      (∏ i ∈ s, p i ^ m i).coeff ((∑ i ∈ s, m i) * d) = ∏ i ∈ s, (p i).coeff d ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, add_mul]
    have hpa : (p a ^ m a).natDegree ≤ m a * d :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hp a))
    refine ⟨natDegree_mul_le.trans (add_le_add hpa ih1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hpa ih1, coeff_pow_of_natDegree_le (hp a), ih2, Finset.prod_insert ha]

theorem form_bound {k σ : Type} [Field k] [Infinite k] [Fintype σ] (n : ℕ)
    (F : MvPolynomial σ k[X]) (hF : F.IsHomogeneous n) (h0 : F ≠ 0) :
    ∃ (c : ℕ) (lam : σ → k),
      (∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (MvPolynomial.eval p F).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) → (∀ i, (p i).coeff d = lam i) →
        (MvPolynomial.eval p F).coeff (n * d + c) ≠ 0 := by
  classical
  set c := F.support.sup (fun m => (F.coeff m).natDegree) with hc
  set G : MvPolynomial σ k := ∑ m ∈ F.support, MvPolynomial.monomial m ((F.coeff m).coeff c) with hG
  have hsumdeg : ∀ m ∈ F.support, ∑ i ∈ m.support, m i = n := by
    intro m hm
    have h := hF (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  have hcle : ∀ m ∈ F.support, (F.coeff m).natDegree ≤ c := fun m hm =>
    Finset.le_sup (f := fun m => (F.coeff m).natDegree) hm
  have hG0 : G ≠ 0 := by
    have hne : F.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
    obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image F.support (fun m => (F.coeff m).natDegree) hne
    have hcm : c = (F.coeff m0).natDegree :=
      le_antisymm (Finset.sup_le fun m hm => hmax m hm) (hcle m0 hm0)
    intro hG'
    have h1 := congrArg (MvPolynomial.coeff m0) hG'
    rw [hG, MvPolynomial.coeff_sum, Finset.sum_eq_single m0] at h1
    · rw [MvPolynomial.coeff_monomial, if_pos rfl, hcm, MvPolynomial.coeff_zero] at h1
      exact (MvPolynomial.mem_support_iff.mp hm0) (Polynomial.leadingCoeff_eq_zero.mp h1)
    · intro m _ hm
      rw [MvPolynomial.coeff_monomial, if_neg hm]
    · intro h
      exact absurd hm0 h
  obtain ⟨lam, hlam⟩ : ∃ lam : σ → k, MvPolynomial.eval lam G ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hG0 (MvPolynomial.funext fun x => by simpa using hall x)
  refine ⟨c, lam, ?_, ?_⟩
  · intro d p hp
    rw [MvPolynomial.eval_eq]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    have hdeg := (prod_pow_bound m.support m p d hp).1
    rw [hsumdeg m hm] at hdeg
    refine natDegree_mul_le.trans ?_
    have := hcle m hm
    omega
  · intro d p hp hpl
    rw [MvPolynomial.eval_eq, Polynomial.finset_sum_coeff]
    have hterm : ∀ m ∈ F.support, (F.coeff m * ∏ i ∈ m.support, p i ^ m i).coeff (n * d + c) =
        (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      intro m hm
      have hb := prod_pow_bound m.support m p d hp
      rw [hsumdeg m hm] at hb
      rw [add_comm (n * d) c, coeff_mul_add_eq_of_natDegree_le (hcle m hm) hb.1, hb.2]
      simp [hpl]
    rw [Finset.sum_congr rfl hterm]
    have hev : MvPolynomial.eval lam G =
        ∑ m ∈ F.support, (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      rw [hG, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.eval_monomial, Finsupp.prod]
    rw [← hev]
    exact hlam

theorem exists_norm_form {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (b : Module.Basis (Fin n) R A) :
    ∃ F : MvPolynomial (Fin n) R, F.IsHomogeneous n ∧
      ∀ p : Fin n → R, MvPolynomial.eval p F = Algebra.norm R (∑ i, p i • b i) := by
  classical
  refine ⟨(Matrix.of fun a c => ∑ i, MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) *
      MvPolynomial.X i).det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    have hC : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) R) =
        MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
    rw [hC]
    have hent : ∀ a ∈ (Finset.univ : Finset (Fin n)), ((Matrix.of fun a c => ∑ i,
        MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) * MvPolynomial.X i) (σ a) a).IsHomogeneous 1 := by
      intro a _
      rw [Matrix.of_apply]
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) (Algebra.leftMulMatrix b (b i) (σ a) a)).mul
        (MvPolynomial.isHomogeneous_X R i)
    have hmul := (MvPolynomial.isHomogeneous_C (Fin n) ((Equiv.Perm.sign σ : ℤ) : R)).mul
      (MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) hent)
    simpa using hmul
  · intro p
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext a c
    simp [map_sum, Matrix.sum_apply, mul_comm]

theorem norm_degree (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) :
    ∃ (c : ℕ) (lam : Fin n → k),
      (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < (d : WithBot ℕ)) →
        ∑ i, (C (lam i) * X ^ d + p i) • b i ≠ 0 ∧
          (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c := by
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  obtain ⟨F, hFh, hFev⟩ := exists_norm_form n b
  have hF0 : F ≠ 0 := by
    intro hF
    have h1 := hFev (fun i => b.repr 1 i)
    rw [hF, map_zero, b.sum_repr 1, map_one] at h1
    exact one_ne_zero h1.symm
  obtain ⟨c, lam, hb1, hb2⟩ := form_bound n F hFh hF0
  refine ⟨c, lam, fun d p hp => ?_, fun d p hp => ?_⟩
  · rw [← hFev]
    exact hb1 d p hp
  · have hq1 : ∀ i, (C (lam i) * X ^ d + p i).natDegree ≤ d := fun i =>
      (natDegree_add_le _ _).trans
        (max_le (natDegree_C_mul_X_pow_le _ _) (natDegree_le_of_degree_le (hp i).le))
    have hq2 : ∀ i, (C (lam i) * X ^ d + p i).coeff d = lam i := fun i => by
      rw [coeff_add, coeff_C_mul_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt (hp i), add_zero]
    have hN : (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).coeff (n * d + c) ≠ 0 := by
      rw [← hFev]
      exact hb2 d (fun i => C (lam i) * X ^ d + p i) hq1 hq2
    refine ⟨fun h0 => hN (by rw [h0, Algebra.norm_zero, coeff_zero]), ?_⟩
    apply le_antisymm
    · rw [← hFev]
      exact hb1 d (fun i => C (lam i) * X ^ d + p i) hq1
    · exact le_natDegree_of_ne_zero hN

end GlobalTheory.NormFormBound
