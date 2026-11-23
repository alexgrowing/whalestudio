import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

private theorem evalAt_polynomialEmbed {n : ℕ} (z : Fin n → ℂˣ) (Q : MvPolynomial (Fin n) ℂ) :
    evalAt z (polyEmb n Q) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) Q := by
  have h : (evalAt z).comp (polyEmb n) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, polyEmb_X, evalAt_single, MvPolynomial.aeval_X, one_mul,
      monomialChar_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact AlgHom.congr_fun h Q

private theorem baseChange_polynomialEmbed {n : ℕ} (l : ℕ) (Q : MvPolynomial (Fin n) ℂ) :
    bc l (polyEmb n Q) = polyEmb n (MvPolynomial.expand l Q) := by
  have h : (bc l).comp (polyEmb n) = (polyEmb n).comp (MvPolynomial.expand l) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.expand_X, map_pow, polyEmb_X,
      AddMonoidAlgebra.single_pow, one_pow]
    simp [bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]
  exact AlgHom.congr_fun h Q

private theorem aeval_elemSymm_power {n : ℕ} (l : ℕ) (i : Fin n) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (powE l i) =
      MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)) := by
  have h := (MvPolynomial.esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
    ⟨MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)), fun w => by
      rw [MvPolynomial.rename_expand, MvPolynomial.esymm_isSymmetric]⟩
  have h2 := congrArg Subtype.val h
  rw [← MvPolynomial.esymmAlgHom_apply]
  exact h2

private theorem aeval_aeval_elemSymm_power {n : ℕ} (l : ℕ) (γ : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))
        (MvPolynomial.aeval (powE l) γ) =
      MvPolynomial.expand l
        (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) := by
  have h : (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))).comp
        (MvPolynomial.aeval (powE l)) =
      (MvPolynomial.expand l).comp
        (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      aeval_elemSymm_power]
  exact AlgHom.congr_fun h γ

private theorem polynomialEmbed_symmetric_mem {n : ℕ} (γ : MvPolynomial (Fin n) ℂ) :
    polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) ∈
      symmetricLaurent n := by
  intro σ
  have h := (MvPolynomial.esymmAlgHom (Fin n) ℂ n γ).2
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.mem_symmetricSubalgebra] at h
  rw [← polyEmb_rename, h σ]

theorem UpperTheory.ConvolutionTheory.H.polyAlg :
    ∀ n : ℕ,
      (∀ g ∈ symmetricLaurent n, g ∈ (polyEmb n).range → ∃ γ : MvPolynomial (Fin n) ℂ, polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) = g) ∧
      (∀ (γ : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂˣ), evalAt z (polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ)) =
        MvPolynomial.eval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1)) γ) ∧
      (∀ (l : ℕ) (γ : MvPolynomial (Fin n) ℂ), bc l (polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ)) = polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (MvPolynomial.aeval (powE l) γ))) ∧
      ∀ D : ℕ, ∃ P : Finset (LaurentRing n), (∀ y ∈ P, y ∈ symmetricLaurent n) ∧
        ∀ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D → polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) ∈ Submodule.span ℂ (P : Set (LaurentRing n)) := by
  intro n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro g hg ⟨Q, rfl⟩
    have hQ : Q ∈ MvPolynomial.symmetricSubalgebra (Fin n) ℂ := by
      rw [MvPolynomial.mem_symmetricSubalgebra]
      intro σ
      apply polyEmb_injective
      rw [polyEmb_rename]
      exact hg σ
    obtain ⟨γ, hγ⟩ := MvPolynomial.esymmAlgHom_surjective ℂ (σ := Fin n) (n := n)
      (Fintype.card_fin n).le ⟨Q, hQ⟩
    refine ⟨γ, ?_⟩
    rw [← MvPolynomial.esymmAlgHom_apply, hγ]
    rfl
  · intro γ z
    rw [evalAt_polynomialEmbed]
    have h : (MvPolynomial.aeval (fun j : Fin n => (z j : ℂ))).comp
          (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) =
        MvPolynomial.aeval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1)) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_esymm_eq_multiset_esymm]
    have h2 := AlgHom.congr_fun h γ
    rw [AlgHom.comp_apply] at h2
    rw [h2, MvPolynomial.aeval_eq_eval]
  · intro l γ
    rw [baseChange_polynomialEmbed, aeval_aeval_elemSymm_power]
  · intro D
    classical
    let f : (Fin n → Fin (D + 1)) → LaurentRing n := fun c =>
      polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (c i : ℕ)) (1 : ℂ)))
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · intro y hy
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
      exact polynomialEmbed_symmetric_mem _
    · intro p hp
      rw [p.as_sum, map_sum, map_sum]
      refine Submodule.sum_mem _ fun s hs => ?_
      have hle : ∀ i, s i < D + 1 := fun i => by
        have h1 : s.degree ≤ p.totalDegree := MvPolynomial.le_totalDegree hs
        have h2 : s i ≤ s.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hm : MvPolynomial.monomial s (MvPolynomial.coeff s p) =
          MvPolynomial.coeff s p • MvPolynomial.monomial s (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hm, map_smul, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun i => ⟨s i, hle i⟩, Finset.mem_univ _, ?_⟩)
      have hs' : (Finsupp.equivFunOnFinite.symm fun i => s i) = s := by
        ext i
        rfl
      simp only [f, hs']
