import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

noncomputable def hTX5 {κ : Type} [Fintype κ] (f : MvPolynomial κ K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w f)) +
      ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)

noncomputable def bilinearSubstitution {D N : ℕ} (f : KTp K D N) :
    MvPolynomial ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) K :=
  MvPolynomial.aeval (fun t : TVar D N =>
    MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
      MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2))) f

section Gen

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] {P I : Type*} [Fintype P]
  [Fintype I]

theorem aeval_elim_mul_of_xhom (f : P → S) (g : I → S) (t : S) (n : ℕ) (Q : MvPolynomial (P ⊕ I) R)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    MvPolynomial.aeval (Sum.elim f (fun i => t * g i)) Q =
      t ^ n * MvPolynomial.aeval (Sum.elim f g) Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, MvPolynomial.aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hQ s hs]
  ring

end Gen

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def affineCoord (c : ι) (j : Fin (d.N + 1)) : Ω c :=
  ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)

noncomputable def linearSubstitution (c : ι) :
    MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K]
      MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X p
    | Sum.inr i => ∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (d.affineCoord c j)

noncomputable def scaledSubstitution (c : ι) :
    MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K →ₐ[K]
      MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X (some p)
    | Sum.inr i => MvPolynomial.X none *
        ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j)

theorem scaledSubstitution_eq (c : ι) : d.scaledSubstitution c = MvPolynomial.aeval (Sum.elim (fun p => MvPolynomial.X (some p))
    (fun i => MvPolynomial.X none *
      ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) := by
  unfold scaledSubstitution
  congr 1
  funext v
  cases v <;> rfl

theorem aeval_elim_eq_rename_linearSubstitution (c : ι)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) :
    MvPolynomial.aeval (Sum.elim (fun p => (MvPolynomial.X (some p) :
        MvPolynomial (Option (Fin (d.D + 2) × Fin (d.N + 1))) (Ω c)))
      (fun i => ∑ j, MvPolynomial.X (some (i, j)) * MvPolynomial.C (d.affineCoord c j))) Q =
      MvPolynomial.rename some (d.linearSubstitution c Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [linearSubstitution, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    cases v <;> simp [linearSubstitution, map_mul, hp, map_sum]

theorem scaledSubstitution_of_homogeneous (c : ι) (n : ℕ)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    d.scaledSubstitution c Q = MvPolynomial.X none ^ n * MvPolynomial.rename some (d.linearSubstitution c Q) := by
  rw [scaledSubstitution_eq, aeval_elim_mul_of_xhom _ _ _ n Q hQ, aeval_elim_eq_rename_linearSubstitution]

theorem eq_zero_of_xhom_zero (c : ι)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = 0) (h : d.linearSubstitution c Q = 0) : Q = 0 := by
  have hvars : (↑Q.vars : Set ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2))) ⊆ Set.range Sum.inl := by
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_vars] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    cases x with
    | inl p => exact ⟨p, rfl⟩
    | inr i =>
      exfalso
      have h0 := (Finset.sum_eq_zero_iff.mp (hQ s hs)) i (Finset.mem_univ _)
      exact (Finsupp.mem_support_iff.mp hxs) h0
  obtain ⟨Q0, rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q Sum.inl Sum.inl_injective hvars
  have hmap : ∀ q : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) K,
      MvPolynomial.aeval (fun p => (MvPolynomial.X p : MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (Ω c))) q =
        MvPolynomial.map (algebraMap K (Ω c)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [MvPolynomial.algebraMap_eq]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p v hp => simp [map_mul, hp]
  have e : d.linearSubstitution c (MvPolynomial.rename Sum.inl Q0) = MvPolynomial.map (algebraMap K (Ω c)) Q0 := by
    rw [← hmap, linearSubstitution, MvPolynomial.aeval_rename]
    rfl
  rw [e] at h
  have hQ0 : Q0 = 0 := MvPolynomial.map_injective _ (algebraMap K (Ω c)).injective (by rw [h, map_zero])
  rw [hQ0, map_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
