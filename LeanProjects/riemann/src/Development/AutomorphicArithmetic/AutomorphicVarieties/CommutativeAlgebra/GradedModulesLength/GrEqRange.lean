import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private noncomputable def monoL (m : Fin k →₀ ℕ) : lat N m →ₗ[B] rees N where
  toFun f := mono N m f.1 f.2
  map_add' f g := Subtype.ext (by
    show MvPolynomial.monomial m (f.1 + g.1) = MvPolynomial.monomial m f.1 + MvPolynomial.monomial m g.1
    rw [map_add])
  map_smul' c f := Subtype.ext (by
    show MvPolynomial.monomial m (c • f.1) = c • MvPolynomial.monomial m f.1
    rw [MvPolynomial.smul_monomial])

private theorem eq_mono {m : Fin k →₀ ℕ} {p : rees N} (hp : p ∈ reesGr N (toDeg m)) :
    p = mono N m (MvPolynomial.coeff m p.1) (p.2 m) := by
  classical
  apply Subtype.ext
  ext n
  show _ = MvPolynomial.coeff n (MvPolynomial.monomial m _)
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · rw [h]
  · exact hp n fun h' => h (toDeg_injective h').symm

private theorem gr_eq_range (m : Fin k →₀ ℕ) : reesGr N (toDeg m) = LinearMap.range (monoL N m) := by
  apply le_antisymm
  · intro p hp
    exact ⟨⟨_, p.2 m⟩, (eq_mono N hp).symm⟩
  · rintro _ ⟨f, rfl⟩
    exact mono_mem N m f.1 f.2

private theorem e_eq (i : Fin k) : e i = toDeg (Finsupp.single i 1) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [e, toDeg]
  · simp [e, toDeg, Pi.single_apply, h, Finsupp.single_apply, Ne.symm h]

private theorem gr_add (m m' : Fin k →₀ ℕ) :
    reesGr N (toDeg (m + m')) = reesGr N (toDeg m) * reesGr N (toDeg m') := by
  apply le_antisymm
  · intro p hp
    have hf : MvPolynomial.coeff (m + m') p.1 ∈ lat N m * lat N m' := by
      rw [← lat_add]
      exact p.2 (m + m')
    obtain ⟨q, hq, hqv⟩ : ∃ q ∈ reesGr N (toDeg m) * reesGr N (toDeg m'),
        q.1 = MvPolynomial.monomial (m + m') (MvPolynomial.coeff (m + m') p.1) := by
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        refine ⟨mono N m a ha * mono N m' b hb,
          Submodule.mul_mem_mul (mono_mem N m a ha) (mono_mem N m' b hb), ?_⟩
        show MvPolynomial.monomial m a * MvPolynomial.monomial m' b = _
        rw [MvPolynomial.monomial_mul]
      · rintro x y ⟨q₁, h₁, e₁⟩ ⟨q₂, h₂, e₂⟩
        refine ⟨q₁ + q₂, add_mem h₁ h₂, ?_⟩
        rw [map_add, ← e₁, ← e₂]
        rfl
    have hpq : p = q := by
      apply Subtype.ext
      rw [hqv]
      exact congrArg Subtype.val (eq_mono N hp)
    rw [hpq]
    exact hq
  · rw [Submodule.mul_le]
    intro a ha b hb
    have hab : MvPolynomial.coeff m a.1 * MvPolynomial.coeff m' b.1 ∈ lat N (m + m') := by
      rw [lat_add]
      exact Submodule.mul_mem_mul (a.2 m) (b.2 m')
    have h : a * b = mono N (m + m') _ hab := by
      apply Subtype.ext
      show a.1 * b.1 = MvPolynomial.monomial (m + m') _
      rw [← MvPolynomial.monomial_mul]
      exact congrArg₂ (· * ·) (congrArg Subtype.val (eq_mono N ha)) (congrArg Subtype.val (eq_mono N hb))
    rw [h]
    exact mono_mem N (m + m') _ hab

end

theorem UpperTheory.V.Alg.M.std_holds :
    ∀ (B A : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [CommRing A] [Algebra B A] (k : ℕ)
      (N : Fin k → Submodule B A), (∀ i, (N i).FG) → Std (reesGr N) := by
  intro B A _ _ hB _ _ k N hN
  have hdeg : ∀ d : Deg k, 0 ≤ d → ∃ m : Fin k →₀ ℕ, toDeg m = d := by
    intro d hd
    refine ⟨Finsupp.equivFunOnFinite.symm (fun j => (d j).toNat), ?_⟩
    funext j
    simp [toDeg, Int.toNat_of_nonneg (hd j)]
  refine ⟨hB, ?_, ?_, ?_, ?_⟩
  · intro d hd
    refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
    apply Subtype.ext
    ext m
    have hnn : 0 ≤ toDeg m := fun j => by simp [toDeg]
    have hm : toDeg m ≠ d := fun h => hd (h ▸ hnn)
    simpa using hp m hm
  · have h0 : (0 : Deg k) = toDeg 0 := by
      funext j
      simp [toDeg]
    rw [h0, gr_eq_range]
    ext p
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨⟨f, hf⟩, rfl⟩
      have hf' := hf
      rw [lat_zero, Submodule.mem_one] at hf'
      obtain ⟨b, hb⟩ := hf'
      refine ⟨b, Subtype.ext ?_⟩
      show algebraMap B (MvPolynomial (Fin k) A) b = MvPolynomial.monomial 0 f
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_apply, hb]
    · rintro ⟨b, rfl⟩
      have hb : algebraMap B A b ∈ lat N 0 := by
        rw [lat_zero]
        exact Submodule.algebraMap_mem b
      refine ⟨⟨algebraMap B A b, hb⟩, Subtype.ext ?_⟩
      show MvPolynomial.monomial 0 (algebraMap B A b) = algebraMap B (MvPolynomial (Fin k) A) b
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.C_apply]
  · intro i
    rw [e_eq, gr_eq_range, LinearMap.range_eq_map]
    refine Submodule.FG.map _ ((Submodule.fg_top _).2 ?_)
    rw [lat_single]
    exact hN i
  · intro d i hd
    obtain ⟨m, rfl⟩ := hdeg d hd
    rw [e_eq, ← toDeg_add, gr_add]
