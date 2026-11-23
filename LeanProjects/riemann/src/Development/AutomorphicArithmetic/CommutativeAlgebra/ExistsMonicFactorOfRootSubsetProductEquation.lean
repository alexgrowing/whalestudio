import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPolynomialEqMapEvalRootsOfPermInvariant

noncomputable section
open Polynomial

private lemma exists_roots {A : Type} [CommRing A] [Nontrivial A] {g : A[X]} (hg : g.Monic) {N : ℕ}
    (hN : g.natDegree = N) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra A S), Function.Injective (algebraMap A S) ∧
      ∃ x : Fin N → S, g.map (algebraMap A S) = ∏ i, (X - C (x i)) := by
  induction N generalizing A with
  | zero =>
    refine ⟨A, inferInstance, Algebra.id A, Function.injective_id, Fin.elim0, ?_⟩
    have h1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg hN
    simp [h1]
  | succ N ih =>
    have hinj : Function.Injective (AdjoinRoot.of g) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h
      exact AdjoinRoot.mk_ne_zero_of_natDegree_lt hg (C_ne_zero.mpr h)
        (by rw [natDegree_C]; omega) (by rwa [AdjoinRoot.mk_C])
    haveI : Nontrivial (AdjoinRoot g) := hinj.nontrivial
    have hroot : (g.map (AdjoinRoot.of g)).IsRoot (AdjoinRoot.root g) := AdjoinRoot.isRoot_root g
    have hfac : (X - C (AdjoinRoot.root g)) * ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g)))
        = g.map (AdjoinRoot.of g) := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hqm : ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g))).Monic :=
      Monic.of_mul_monic_left (monic_X_sub_C _) (hfac ▸ hg.map _)
    have hqd : ((g.map (AdjoinRoot.of g)) /ₘ (X - C (AdjoinRoot.root g))).natDegree = N := by
      have e1 := congrArg Polynomial.natDegree hfac
      rw [(monic_X_sub_C _).natDegree_mul hqm, natDegree_X_sub_C,
        natDegree_map_eq_of_injective hinj, hN] at e1
      omega
    obtain ⟨S, iS, aS, hSinj, x, hx⟩ := ih hqm hqd
    letI : Algebra A S := ((algebraMap (AdjoinRoot g) S).comp (AdjoinRoot.of g)).toAlgebra
    refine ⟨S, iS, this, hSinj.comp hinj, Fin.cons (algebraMap (AdjoinRoot g) S (AdjoinRoot.root g)) x, ?_⟩
    have e2 : g.map (algebraMap A S) = (g.map (AdjoinRoot.of g)).map (algebraMap (AdjoinRoot g) S) := by
      rw [Polynomial.map_map]
      rfl
    rw [e2, ← hfac, Polynomial.map_mul, hx, Fin.prod_univ_succ]
    simp

private lemma idem_mul {S ι : Type} [CommRing S] (Λ : Finset ι) (ε : ι → S) (a b : ι → S[X])
    (G : S[X]) (h1 : ∑ J ∈ Λ, ε J = 1) (h0 : ∀ J ∈ Λ, ∀ J' ∈ Λ, J ≠ J' → ε J * ε J' = 0)
    (hab : ∀ J ∈ Λ, a J * b J = G) :
    (∑ J ∈ Λ, C (ε J) * a J) * (∑ J ∈ Λ, C (ε J) * b J) = G := by
  have hsq : ∀ J ∈ Λ, ε J * ε J = ε J := by
    intro J hJ
    have e := congrArg (ε J * ·) h1
    simp only [mul_one, Finset.mul_sum] at e
    rwa [Finset.sum_eq_single J (fun J' hJ' hne => h0 J hJ J' hJ' (Ne.symm hne))
      (fun h => absurd hJ h)] at e
  rw [Finset.sum_mul_sum]
  calc ∑ J ∈ Λ, ∑ J' ∈ Λ, C (ε J) * a J * (C (ε J') * b J')
      = ∑ J ∈ Λ, C (ε J) * G := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [Finset.sum_eq_single J]
        · rw [← hab J hJ]
          calc C (ε J) * a J * (C (ε J) * b J) = C (ε J * ε J) * (a J * b J) := by
                rw [C_mul]
                ring
            _ = C (ε J) * (a J * b J) := by rw [hsq J hJ]
        · intro J' hJ' hne
          have e : C (ε J) * C (ε J') = 0 := by
            rw [← C_mul, h0 J hJ J' hJ' (Ne.symm hne), C_0]
          calc C (ε J) * a J * (C (ε J') * b J') = (C (ε J) * C (ε J')) * (a J * b J') := by ring
            _ = 0 := by rw [e, zero_mul]
        · intro h
          exact absurd hJ h
    _ = G := by rw [← Finset.sum_mul, ← map_sum, h1, C_1, one_mul]

private lemma weights {S ι : Type} [CommRing S] [DecidableEq ι] (Λ : Finset ι) (t : ι → S)
    (c c' : S) (hc : c' * c = 1) (h0 : ∏ J ∈ Λ, t J = 0)
    (h1 : ∑ J ∈ Λ, ∏ J' ∈ Λ.erase J, t J' = c) :
    (∑ J ∈ Λ, c' * ∏ J' ∈ Λ.erase J, t J' = 1) ∧
    (∀ J ∈ Λ, ∀ J' ∈ Λ, J ≠ J' →
      (c' * ∏ K ∈ Λ.erase J, t K) * (c' * ∏ K ∈ Λ.erase J', t K) = 0) ∧
    (∀ J ∈ Λ, (c' * ∏ K ∈ Λ.erase J, t K) * t J = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Finset.mul_sum, h1, hc]
  · intro J hJ J' hJ' hne
    have hmem : J' ∈ Λ.erase J := Finset.mem_erase.mpr ⟨Ne.symm hne, hJ'⟩
    rw [← Finset.mul_prod_erase (Λ.erase J) t hmem]
    have h2 : t J' * ∏ K ∈ Λ.erase J', t K = 0 := by rw [Finset.mul_prod_erase Λ t hJ', h0]
    calc c' * (t J' * ∏ K ∈ (Λ.erase J).erase J', t K) * (c' * ∏ K ∈ Λ.erase J', t K)
        = c' * c' * (∏ K ∈ (Λ.erase J).erase J', t K) * (t J' * ∏ K ∈ Λ.erase J', t K) := by ring
      _ = 0 := by rw [h2, mul_zero]
  · intro J hJ
    rw [mul_assoc, Finset.prod_erase_mul Λ t hJ, h0, mul_zero]

private def Wt {A : Type} [CommRing A] (N m : ℕ) (α c' : A) (J : Finset (Fin N)) :
    MvPolynomial (Fin N) A :=
  MvPolynomial.C c' * ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J,
    (MvPolynomial.C α - ∏ i ∈ J', MvPolynomial.X i)

private def Ph {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) : (MvPolynomial (Fin N) A)[X] :=
  ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
    C (Wt N m α c' J) * ∏ i ∈ f J, (X - C (MvPolynomial.X i))

private lemma Wt_rename {A : Type} [CommRing A] (N m : ℕ) (α c' : A) (σ : Equiv.Perm (Fin N))
    (J : Finset (Fin N)) :
    MvPolynomial.rename σ (Wt N m α c' J) = Wt N m α c' (J.map σ.toEmbedding) := by
  unfold Wt
  rw [map_mul, MvPolynomial.rename_C, map_prod]
  congr 1
  refine Finset.prod_equiv (Equiv.finsetCongr σ) ?_ ?_
  · intro K
    simp [Finset.mem_erase, Finset.mem_powersetCard]
  · intro K _
    simp [map_sub, map_prod, MvPolynomial.rename_X, Finset.prod_map]

private lemma Ph_sym {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N))
    (hf : ∀ (σ : Equiv.Perm (Fin N)) J, f (J.map σ.toEmbedding) = (f J).map σ.toEmbedding)
    (σ : Equiv.Perm (Fin N)) :
    (Ph N m α c' f).map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom =
      Ph N m α c' f := by
  unfold Ph
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Wt_rename,
    MvPolynomial.rename_X]
  refine Finset.sum_nbij' (fun J => J.map σ.toEmbedding) (fun J => J.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    simpa using hJ
  · intro J hJ
    simpa using hJ
  · intro J _
    ext i
    simp [Finset.mem_map_equiv]
  · intro J _
    ext i
    simp [Finset.mem_map_equiv]
  · intro J _
    rw [hf σ J, Finset.prod_map]
    rfl

private lemma Ph_deg {A : Type} [CommRing A] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) (d : ℕ)
    (hd : ∀ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (f J).card = d) :
    (Ph N m α c' f).natDegree ≤ d := by
  unfold Ph
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro J hJ
  have e1 : ∑ i ∈ f J, (X - C (MvPolynomial.X i : MvPolynomial (Fin N) A)).natDegree ≤ (f J).card := by
    have e2 := Finset.sum_le_sum (s := f J)
      (f := fun i => (X - C (MvPolynomial.X i : MvPolynomial (Fin N) A)).natDegree)
      (g := fun _ => (1 : ℕ)) (fun i _ => natDegree_X_sub_C_le _)
    simpa using e2
  rw [← hd J hJ]
  exact (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans e1)

private lemma Ph_map {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (N m : ℕ) (α c' : A)
    (f : Finset (Fin N) → Finset (Fin N)) (x : Fin N → S) :
    (Ph N m α c' f).map (MvPolynomial.aeval x : MvPolynomial (Fin N) A →ₐ[A] S).toRingHom =
      ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
        C (algebraMap A S c' * ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J,
            (algebraMap A S α - ∏ i ∈ J', x i)) * ∏ i ∈ f J, (X - C (x i)) := by
  unfold Ph Wt
  simp [Polynomial.map_sum, Polynomial.map_prod, map_prod, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C]

private lemma coeff_sum {S ι : Type} [CommRing S] [Nontrivial S] {N : ℕ} (Λ : Finset ι)
    (ε : ι → S) (s : ι → Finset (Fin N)) (x : Fin N → S) (d : ℕ)
    (hd : ∀ J ∈ Λ, (s J).card = d) :
    (∑ J ∈ Λ, C (ε J) * ∏ i ∈ s J, (X - C (x i))).coeff d = ∑ J ∈ Λ, ε J := by
  rw [finset_sum_coeff]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [coeff_C_mul]
  have hm : (∏ i ∈ s J, (X - C (x i))).Monic :=
    monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)
  have hdeg : (∏ i ∈ s J, (X - C (x i))).natDegree = d := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (x i)]
    simp [hd J hJ]
  rw [← hdeg, hm.coeff_natDegree, mul_one]

private lemma eval_sum {S ι : Type} [CommRing S] {N : ℕ} (Λ : Finset ι) (ε : ι → S)
    (s : ι → Finset (Fin N)) (x : Fin N → S) (a : S) (d : ℕ) (h1 : ∑ J ∈ Λ, ε J = 1)
    (hd : ∀ J ∈ Λ, (s J).card = d) (h3 : ∀ J ∈ Λ, ε J * (a - ∏ i ∈ s J, x i) = 0) :
    (∑ J ∈ Λ, C (ε J) * ∏ i ∈ s J, (X - C (x i))).eval 0 = (-1) ^ d * a := by
  rw [eval_finset_sum]
  have key : ∀ J ∈ Λ, (C (ε J) * ∏ i ∈ s J, (X - C (x i))).eval 0 = (-1) ^ d * (ε J * a) := by
    intro J hJ
    have h := h3 J hJ
    rw [eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    rw [Finset.prod_neg, hd J hJ]
    have e : ε J * ∏ i ∈ s J, x i = ε J * a := by linear_combination -h
    linear_combination (-1) ^ d * e
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← Finset.sum_mul, h1, one_mul]

theorem UpperTheory.exists_monic_factor_of_root_subset_product_equation :
    ∀ (A : Type) [CommRing A] (g : A[X]) (n m N : ℕ), n + m = N → g.Monic → g.natDegree = N → ∀ (α : A) (c : Aˣ),
      (∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (algebraMap A S α - ∏ i ∈ J, x i) = 0 ∧
        ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J, (algebraMap A S α - ∏ i ∈ J', x i) = algebraMap A S c) →
      ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧ Q.natDegree ≤ m ∧ Q.coeff m = 1 ∧ Q.eval 0 = (-1) ^ m * α := by
  intro A _ g n m N hnm hg hN α c hyp
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _, by simp,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  classical
  obtain ⟨q, hqdeg, hq⟩ := UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Ph N m α (↑c⁻¹ : A) (fun J => J))
    (Ph_sym N m α _ _ (fun σ J => rfl))
  obtain ⟨p, -, hp⟩ := UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Ph N m α (↑c⁻¹ : A) (fun J => Jᶜ))
    (Ph_sym N m α _ _ (fun σ J => by ext i; simp [Finset.mem_map_equiv]))
  obtain ⟨S, iS, aS, hinj, x, hx⟩ := exists_roots hg hN
  haveI : Nontrivial S := hinj.nontrivial
  have hinjX : Function.Injective (Polynomial.map (algebraMap A S)) := Polynomial.map_injective _ hinj
  obtain ⟨h0, h1⟩ := hyp S x hx
  have hc : algebraMap A S (↑c⁻¹ : A) * algebraMap A S (↑c : A) = 1 := by
    rw [← map_mul]
    simp
  obtain ⟨w1, w2, w3⟩ := weights (Finset.powersetCard m (Finset.univ : Finset (Fin N)))
    (fun J => algebraMap A S α - ∏ i ∈ J, x i) _ _ hc h0 h1
  have hqS := hq S x hx
  rw [Ph_map] at hqS
  have hpS := hp S x hx
  rw [Ph_map] at hpS
  have hQd : q.natDegree ≤ m :=
    hqdeg.trans (Ph_deg N m α _ _ m (fun J hJ => (Finset.mem_powersetCard.mp hJ).2))
  have hQc : q.coeff m = 1 := by
    apply hinj
    rw [← Polynomial.coeff_map, hqS,
      coeff_sum _ _ (fun J => J) x m (fun J hJ => (Finset.mem_powersetCard.mp hJ).2), w1, map_one]
  have hQm : q.Monic := by
    have e : q.natDegree = m := natDegree_eq_of_le_of_coeff_ne_zero hQd (by rw [hQc]; exact one_ne_zero)
    rw [Monic, leadingCoeff, e, hQc]
  have hg' : g = p * q := by
    apply hinjX
    rw [Polynomial.map_mul, hpS, hqS, hx]
    exact (idem_mul _ _ (fun J => ∏ i ∈ Jᶜ, (X - C (x i))) (fun J => ∏ i ∈ J, (X - C (x i))) _ w1 w2
      (fun J _ => Finset.prod_compl_mul_prod J _)).symm
  refine ⟨p, q, Monic.of_mul_monic_right hQm (hg' ▸ hg), hQm, hg', hQd, hQc, ?_⟩
  apply hinj
  rw [← Polynomial.eval_zero_map, hqS,
    eval_sum _ _ (fun J => J) x _ m w1 (fun J hJ => (Finset.mem_powersetCard.mp hJ).2) w3]
  simp

end
