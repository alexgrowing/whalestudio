import Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfC

namespace LateralTheory.E.E4

open MvPolynomial

noncomputable def killFirst (k : Type) [Field k] (s j : ℕ) :
    MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin s) k :=
  aeval (fun i => if i.val < j then 0 else X i)

lemma killFirst_X (k : Type) [Field k] (s j : ℕ) (i : Fin s) :
    killFirst k s j (X i) = if i.val < j then 0 else X i := by
  simp [killFirst]

lemma X_mem_ker_killFirst (k : Type) [Field k] (s j : ℕ) (i : Fin s) (hi : i.val < j) :
    (X i : MvPolynomial (Fin s) k) ∈ RingHom.ker (killFirst k s j) := by
  rw [RingHom.mem_ker]; erw [killFirst_X]; simp [hi]

lemma X_not_mem_ker_killFirst (k : Type) [Field k] (s j : ℕ) (i : Fin s) (hi : ¬ i.val < j) :
    (X i : MvPolynomial (Fin s) k) ∉ RingHom.ker (killFirst k s j) := by
  rw [RingHom.mem_ker]; erw [killFirst_X]; simp [hi, X_ne_zero]

theorem LeafNoetherDim_of : LeafNoetherDim := by
  intro k B _ _ _ _ _ _ hB s g hg hf
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have hint : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨fun x => hf.to_isIntegral x⟩
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin s) k) B) := hg
  by_contra hs
  rcases Nat.lt_or_gt_of_ne hs with h0 | h2
  ·
    obtain rfl : s = 0 := by omega
    apply hB
    rw [← Algebra.IsIntegral.isField_iff_isField hinj]
    exact MulEquiv.isField (Field.toIsField k) (isEmptyAlgEquiv k (Fin 0)).toMulEquiv
  ·
    set A := MvPolynomial (Fin s) k
    let P1 : Ideal A := RingHom.ker (killFirst k s 1)
    let P2 : Ideal A := RingHom.ker (killFirst k s 2)
    have hP1 : P1.IsPrime := RingHom.ker_isPrime _
    have hP2 : P2.IsPrime := RingHom.ker_isPrime _
    let i0 : Fin s := ⟨0, by omega⟩
    let i1 : Fin s := ⟨1, by omega⟩
    have h12 : P1 ≤ P2 := by
      intro p hp
      simp only [P1, P2, RingHom.mem_ker] at hp ⊢
      have : killFirst k s 2 = (killFirst k s 2).comp (killFirst k s 1) := by
        apply MvPolynomial.algHom_ext; intro i
        simp only [AlgHom.comp_apply, killFirst_X]
        by_cases h : i.val < 1
        · simp [h, show i.val < 2 by omega]
        · simp [h, killFirst_X]
      rw [this, AlgHom.comp_apply]; erw [hp]; simp
    have x0P1 : (X i0 : A) ∈ P1 := X_mem_ker_killFirst k s 1 i0 (by simp [i0])
    have x1P2 : (X i1 : A) ∈ P2 := X_mem_ker_killFirst k s 2 i1 (by simp [i1])
    have x1P1 : (X i1 : A) ∉ P1 := X_not_mem_ker_killFirst k s 1 i1 (by simp [i1])
    have : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
    have hc0 : Ideal.comap (algebraMap A B) (⊥ : Ideal B) = ⊥ :=
      Ideal.comap_bot_of_injective _ hinj
    obtain ⟨Q1, -, hQ1, hcQ1⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P1 (⊥ : Ideal B) (by rw [hc0]; exact bot_le)
    obtain ⟨Q2, hQ12, hQ2, hcQ2⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P2 Q1 (by rw [hcQ1]; exact h12)
    have hQ1ne : Q1 ≠ ⊥ := by
      rintro rfl
      rw [hc0] at hcQ1
      apply X_ne_zero (R := k) i0
      have : (X i0 : A) ∈ (⊥ : Ideal A) := hcQ1 ▸ x0P1
      simp at this
    have hQ1max : Q1.IsMaximal := hQ1.isMaximal hQ1ne
    have hne : Q1 ≠ Q2 := by
      rintro rfl
      rw [hcQ1] at hcQ2
      exact x1P1 (hcQ2 ▸ x1P2)
    have := hQ1max.eq_of_le hQ2.ne_top hQ12
    exact hne this

end LateralTheory.E.E4
