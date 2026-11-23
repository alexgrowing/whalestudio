import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TracesFromEigenvaluesRank2
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MapTraceEqSumRootsOfCharpolyMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowResDegPlaceNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdmissibleOfNewformAttached
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockConjugateRankThreeRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem trace_conj_gl3 {k : Type} [Field k] (g x : GL (Fin 3) k) :
    ((g * x * g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).trace = (x : Matrix (Fin 3) (Fin 3) k).trace := by
  rw [Units.val_mul, Matrix.trace_mul_comm, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem place_over_rational_prime (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (hw : (p : 𝓞 K) ∈ w.asIdeal) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨w.under (𝓞 ℚ), ?_⟩
  change (p : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  rw [Ideal.mem_comap, map_natCast]
  exact hw

theorem UpperTheory.frobenius_trace_count_bound_of_rat_eigensystem_count :
    CountQ → NewformAut → ∃ c A : ℕ, ∀ (K : Type) [Field K] [NumberField K], ∀ e : ℕ, 1 ≤ e → ∀ M : ℕ, 1 ≤ M → ∀ (p h : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ∃ D : TrData (p ^ h) e, Nat.card D.S ≤ c * (M * (e + 1)) ^ A ∧ ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (p ^ h) σ → D.Classifies ι σ⁻¹ (Adm2 ι e M) := by
  intro hQ hN
  obtain ⟨c, A, hc⟩ := hQ 2 le_rfl
  refine ⟨c, A, ?_⟩
  intro K _ _ e he M hM p h w hp hw hpM
  obtain ⟨v, hv⟩ := place_over_rational_prime K p w hw
  have hanti : StrictAnti (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    omega
  have hrev : ∀ i : Fin 2, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i + (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i.rev = 0 := by
    intro i
    fin_cases i <;> simp [Fin.rev]
  have habs : ∀ i : Fin 2, |(![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i| ≤ (e : ℕ) := by
    intro i
    fin_cases i <;> simp
  obtain ⟨D, hcard, hD⟩ := hc _ 0 hanti hrev e habs M hM p v hp hv hpM
  obtain ⟨T, u, hT⟩ := UpperTheory.traces_from_eigenvalues_rank2 p h e D
  refine ⟨T, (Nat.card_congr u) ▸ hcard, ?_⟩
  intro l _ hl2 hlp Ω _ _ _ _ _ ι B hB σ hσ
  haveI : IsAlgClosure ℚ Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed K
      isAlgebraic := Algebra.IsAlgebraic.trans ℚ K Ω }
  obtain ⟨cl, hcl1, hcl2⟩ := hD l hl2 hlp Ω ι
  obtain ⟨hBv, τ, hτ, hI⟩ := UpperTheory.frobenius_pow_resDeg_place_norm K Ω p h w v hp hw hv B hB σ hσ
  have hex : ∀ r : {r // Adm2 ι e M (K := K) (Ω := Ω) r},
      ∃ W : {W : G ℚ Ω →* GL (Fin 2) (Qbar l) // AdmR ι M ![(e : ℤ), -(e : ℤ)] 0 W},
      ∃ g : GL (Fin 3) (Qbar l), ∀ s : G K Ω,
        ((g * r.1 s * g⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) =
        !![W.1 (s.restrictScalars ℚ) 0 0, 0, W.1 (s.restrictScalars ℚ) 0 1; 0, 1, 0;
          W.1 (s.restrictScalars ℚ) 1 0, 0, W.1 (s.restrictScalars ℚ) 1 1] := by
    rintro ⟨r, W, h1, h2, h3, h4, h5⟩
    exact ⟨⟨W, UpperTheory.admissible_of_newform_attached hN Ω l ι e M he W h1 h2 h3 h4⟩, h5⟩
  choose W g hg using hex
  refine ⟨fun r => u (cl (W r)), fun r r' H => ?_, fun r => ?_⟩
  · exact UpperTheory.block_conjugate_rank_three_rep _ _ _ (fun s : G K Ω => s.restrictScalars ℚ) (W r).1 (W r').1 r.1 r'.1 (g r) (g r')
      (hg r) (hg r') (hcl1 _ _ (u.injective H))
  · obtain ⟨hun, hfr⟩ := hcl2 (W r) B hBv
    have h1 := hun _ hI
    rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h1
    have h2 : (W r).1 ((σ⁻¹).restrictScalars ℚ) = (W r).1 τ⁻¹ ^ h := by
      have : (σ⁻¹).restrictScalars ℚ = (σ.restrictScalars ℚ : G ℚ Ω)⁻¹ := rfl
      rw [this, map_inv, map_inv, ← h1, inv_pow]
    have h3 := (UpperTheory.map_trace_eq_sum_roots_of_charpoly_map (Qbar l) ι.toRingHom _).2 _ (hfr τ hτ) h
    rw [Multiset.map_map] at h3
    rw [hT, ← trace_conj_gl3 (g r), hg r, h2, RingEquiv.eq_symm_apply]
    change _ = 1 + ((D.β (cl (W r))).map ((fun x => x ^ h) ∘ fun x => x⁻¹)).sum
    rw [← h3, ← Units.val_pow_eq_pow_val, Matrix.trace_fin_two, Matrix.trace_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_one, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    ring
