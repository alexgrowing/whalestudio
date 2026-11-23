import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialModelIsometry.IsPolyMon

noncomputable section

namespace PI.WMI

open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem detSplit_fullMinor {N : ℕ} (s : ℕ) (I : Fin s → Fin N) (hs : s ≤ N) (hN : s = N) :
    ∃ e : ℂ, initMinor ℂ (n := N) I hs = C e * detPoly N := by
  subst hN
  by_cases hI : Function.Injective I
  · have hb : Function.Bijective I := (Fintype.bijective_iff_injective_and_card I).2 ⟨hI, rfl⟩
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective I hb) : ℤ) : ℂ), ?_⟩
    have h := Matrix.det_permute (Equiv.ofBijective I hb)
      (Matrix.of fun i j : Fin s => (X (i, j) : MvPolynomial (Fin s × Fin s) ℂ))
    have hM : initMinor ℂ (n := s) I hs =
        ((Matrix.of fun i j : Fin s => (X (i, j) : MvPolynomial (Fin s × Fin s) ℂ)).submatrix
          (Equiv.ofBijective I hb) id).det := by
      unfold initMinor
      congr 1
    rw [hM, h, detPoly, map_intCast]
  · refine ⟨0, ?_⟩
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨i, j, hij, hne⟩ := hI
    rw [map_zero, zero_mul]
    unfold initMinor
    exact Matrix.det_zero_of_row_eq hne (funext fun q => by simp [hij])

theorem detSplit_prodMem {N K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ N) (I : ∀ k, Fin (sz k) → Fin N)
    (s : Finset (Fin K)) :
    ∏ k ∈ s, initMinor ℂ (I k) (hsz k) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (fun t => (s.filter fun k => t.val < sz k).card) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h := (Formalism.GradedWeylDivisibility.dualWeylMul ℂ N N 0 0 1 1).2
    convert h using 2
    · funext t; simp
    · simp
  · intro a s ha ih
    have h1 : initMinor ℂ (I a) (hsz a) ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (shapeDeg (fun _ : Fin 1 => sz a)) := by
      have := Formalism.GradedWeylDivisibility.bidetMem ℂ N N 1 (fun _ => sz a) (fun _ => hsz a) (fun _ => I a)
      simpa only [bideterminant, Fin.prod_univ_one] using this
    have h2 := (Formalism.GradedWeylDivisibility.dualWeylMul ℂ N N _ _ _ _).1 h1 ih
    rw [Finset.prod_insert ha]
    convert h2 using 2
    funext t
    simp only [shapeDeg, Pi.add_apply, Finset.filter_insert]
    split_ifs with ht
    · rw [Finset.card_insert_of_notMem (by simp [ha])]
      simp [ht, add_comm]
    · simp [ht]

theorem determinant_splitting_formula : DetSplit := by
  intro N ν c hν f hf
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨f, ?_, ?_⟩
    · have : (fun a : Fin 0 => ν a + c) = ν := funext fun a => a.elim0
      rwa [this] at hf
    · simp [detPoly]
  · classical
    have h0 := hν hN
    let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
      (Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν).map (LinearMap.mulLeft ℂ (detPoly N ^ c))
    suffices hT : f ∈ T by
      obtain ⟨f', hf', hff⟩ := hT
      exact ⟨f', hf', hff.symm⟩
    rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N] at hf
    refine (Submodule.span_le.2 ?_) hf
    rintro _ ⟨K, sz, hsz, I, hshape, rfl⟩
    let A : Finset (Fin K) := Finset.univ.filter fun k => sz k = N
    have hcard : ∀ t : Fin N, (Finset.univ.filter fun k => t.val < sz k).card =
        (Aᶜ.filter fun k => t.val < sz k).card + A.card := by
      intro t
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_sum_compl A, add_comm,
        Finset.card_eq_sum_ones A]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have : sz k = N := by simpa [A] using hk
      simp [this, t.isLt]
    have hA : A.card = c := by
      have h1 := congrFun hshape ⟨N - 1, by omega⟩
      have h2 := hcard ⟨N - 1, by omega⟩
      have h3 : (Aᶜ.filter fun k => N - 1 < sz k) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k hk hlt
        have hkA : ¬ sz k = N := by simpa [A] using hk
        have := hsz k
        omega
      simp only [shapeDeg] at h1
      rw [h0] at h1
      rw [h3] at h2
      simp at h2
      omega
    have hrest : (fun t : Fin N => (Aᶜ.filter fun k => t.val < sz k).card) = ν := by
      funext t
      have h1 := congrFun hshape t
      simp only [shapeDeg] at h1
      have := hcard t
      omega
    have hmem := detSplit_prodMem sz hsz I Aᶜ
    rw [hrest] at hmem
    have hfac : ∀ k : Fin K, ∃ e : ℂ, k ∈ A → initMinor ℂ (I k) (hsz k) = C e * detPoly N := by
      intro k
      by_cases hk : k ∈ A
      · obtain ⟨e, he⟩ := detSplit_fullMinor (sz k) (I k) (hsz k) (by simpa [A] using hk)
        exact ⟨e, fun _ => he⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose e he using hfac
    refine ⟨C (∏ k ∈ A, e k) * ∏ k ∈ Aᶜ, initMinor ℂ (I k) (hsz k), ?_, ?_⟩
    · rw [C_mul']
      exact Submodule.smul_mem _ _ hmem
    · simp only [LinearMap.mulLeft_apply]
      unfold bideterminant
      rw [← Finset.prod_mul_prod_compl A, Finset.prod_congr rfl fun k hk => he k hk,
        Finset.prod_mul_distrib, Finset.prod_const, hA, map_prod]
      ring

end PI.WMI
