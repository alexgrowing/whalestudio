import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.det_mem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (m : ℕ) (g : Fin m → F.G0) (α : Fin m →₀ ℕ), MvPolynomial.coeff α (∑ a, (MvPolynomial.X a : MvPolynomial (Fin m) S.R) • (S.ρ.r (g a)).map MvPolynomial.C).det ∈ S.B := by
  intro l _ O _ _ _ _ F C₀ n _ _ S m g α
  classical
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  refine sum_mem (fun σ _ => ?_)
  rw [Units.smul_def, MvPolynomial.coeff_smul]
  refine zsmul_mem ?_ _
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum, MvPolynomial.coeff_sum]
  refine sum_mem (fun f _ => ?_)
  rw [Finset.prod_mul_distrib, ← map_prod, mul_comm, MvPolynomial.coeff_C_mul]
  refine mul_mem (S.mon_mem ?_) ?_
  · refine ⟨List.ofFn (fun i => (g (f i), σ i, i)), ?_, ?_⟩
    · rw [List.map_ofFn, List.sum_ofFn]
      simp only [Function.comp_def]
      rw [Finset.sum_sub_distrib, Equiv.sum_comp, sub_self]
    · rw [List.map_ofFn, List.prod_ofFn]
      rfl
  · obtain ⟨d, hd⟩ : ∃ d, ∏ i, (MvPolynomial.X (f i) : MvPolynomial (Fin m) S.R) =
        MvPolynomial.monomial d 1 := by
      refine Finset.prod_induction _ (fun p => ∃ d, p = MvPolynomial.monomial d 1) ?_ ?_ ?_
      · rintro a b ⟨d₁, rfl⟩ ⟨d₂, rfl⟩
        exact ⟨d₁ + d₂, by rw [MvPolynomial.monomial_mul, mul_one]⟩
      · exact ⟨0, by rw [MvPolynomial.monomial_zero', MvPolynomial.C_1]⟩
      · intro i _
        exact ⟨Finsupp.single (f i) 1, rfl⟩
    rw [hd, MvPolynomial.coeff_monomial]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
