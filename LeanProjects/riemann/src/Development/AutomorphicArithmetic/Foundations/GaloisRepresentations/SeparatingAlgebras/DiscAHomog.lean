import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private noncomputable def discA (a n : ℕ) : MvPolynomial (Fin a) ℤ :=
  ∏ p ∈ (Finset.univ : Finset (Fin a)).offDiag, ∏ c ∈ Finset.Icc 1 n,
    (MvPolynomial.X p.1 ^ c - MvPolynomial.X p.2 ^ c)

private noncomputable def discB (a : ℕ) : MvPolynomial (Fin a) ℤ :=
  ∏ q ∈ (Finset.univ : Finset (Fin a × Fin a × Fin a)).filter
      (fun q => ¬ (q.1 = q.2.1 ∧ q.2.2 = q.2.1)),
    (MvPolynomial.X q.1 * MvPolynomial.X q.2.2 - MvPolynomial.X q.2.1 ^ 2)

private theorem discA_symm (a n : ℕ) : (discA a n).IsSymmetric := by
  intro σ
  simp only [discA, map_prod, map_sub, map_pow, MvPolynomial.rename_X]
  refine Finset.prod_equiv (σ.prodCongr σ) ?_ ?_
  · rintro ⟨i, j⟩
    simp [Finset.mem_offDiag]
  · intro p _
    rfl

private theorem discB_symm (a : ℕ) : (discB a).IsSymmetric := by
  intro σ
  simp only [discB, map_prod, map_sub, map_mul, map_pow, MvPolynomial.rename_X]
  refine Finset.prod_equiv (σ.prodCongr (σ.prodCongr σ)) ?_ ?_
  · rintro ⟨i, j, k⟩
    simp
  · intro p _
    rfl

private theorem discA_homog (a n : ℕ) : ∃ d, (discA a n).IsHomogeneous d := by
  refine ⟨_, MvPolynomial.IsHomogeneous.prod _ _ (fun _ => ∑ c ∈ Finset.Icc 1 n, c) fun p _ =>
    MvPolynomial.IsHomogeneous.prod _ _ (fun c => c) fun c _ => ?_⟩
  exact (MvPolynomial.isHomogeneous_X_pow _ _).sub (MvPolynomial.isHomogeneous_X_pow _ _)

private theorem discB_homog (a : ℕ) : ∃ d, (discB a).IsHomogeneous d := by
  refine ⟨_, MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 2) fun q _ => ?_⟩
  exact ((MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _)).sub
    (MvPolynomial.isHomogeneous_X_pow _ _)

private theorem discA_ne (a n : ℕ) : discA a n ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun p hp => Finset.prod_ne_zero_iff.2 fun c hc h => ?_
  have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.1 hp).2.2
  have hc0 : c ≠ 0 := by
    have := (Finset.mem_Icc.1 hc).1
    omega
  have := congrArg (MvPolynomial.eval (Pi.single p.1 (1 : ℤ))) h
  simp [Pi.single_eq_of_ne hne.symm, hc0] at this

private theorem discB_ne (a : ℕ) : discB a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun q hq h => ?_
  have hq' : ¬ (q.1 = q.2.1 ∧ q.2.2 = q.2.1) := (Finset.mem_filter.1 hq).2
  have hz : (Pi.single q.2.1 (1 : ℤ) : Fin a → ℤ) q.1 * (Pi.single q.2.1 (1 : ℤ) : Fin a → ℤ) q.2.2 = 0 := by
    by_cases h1 : q.1 = q.2.1
    · have h2 : q.2.2 ≠ q.2.1 := fun h2 => hq' ⟨h1, h2⟩
      rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul]
  have := congrArg (MvPolynomial.eval (Pi.single q.2.1 (1 : ℤ))) h
  simp only [map_sub, map_mul, map_pow, MvPolynomial.eval_X, map_zero, hz, Pi.single_eq_same] at this
  norm_num at this

theorem UpperTheory.Gal.Gen.discEx2_pf :
    UpperTheory.Gal.Gen.DiscEx2 := by
  intro a n
  have hne : discA a n * discB a ≠ 0 := mul_ne_zero (discA_ne a n) (discB_ne a)
  obtain ⟨d₁, h₁⟩ := discA_homog a n
  obtain ⟨d₂, h₂⟩ := discB_homog a
  have hh := h₁.mul h₂
  refine ⟨discA a n * discB a, ?_, ?_, hne, ?_⟩
  · intro σ
    rw [map_mul, discA_symm a n σ, discB_symm a σ]
  · rw [hh.totalDegree hne]
    exact hh
  · intro k _ z hz
    rw [map_mul] at hz
    have hA := left_ne_zero_of_mul hz
    have hB := right_ne_zero_of_mul hz
    simp only [discA, discB, map_prod, map_sub, map_mul, map_pow, MvPolynomial.aeval_X] at hA hB
    refine ⟨fun i j hij c hc1 hcn => ?_, fun i j k' hq => ?_⟩
    · have h1 := Finset.prod_ne_zero_iff.1 hA (i, j)
        (Finset.mem_offDiag.2 ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩)
      exact sub_ne_zero.1 (Finset.prod_ne_zero_iff.1 h1 c (Finset.mem_Icc.2 ⟨hc1, hcn⟩))
    · exact sub_ne_zero.1 (Finset.prod_ne_zero_iff.1 hB (i, j, k')
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩))
