import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntEqProdOfGaloisPermutedIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdicNormProdLeProdOfInjectiveClasses
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinTraceDifferenceLogBound
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.frobenius_trace_norm_nonzero_log_bound :
    ∀ (q e : ℕ), 7 ≤ q → 1 ≤ e → ∀ (D : TrData q e) (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) → (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) → ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ Fintype.card Orb * Nat.card D.S * (2 * e * Real.log q + 1) ∧ ∀ (l : ℕ) [Fact l.Prime], ¬ l ∣ q → ∀ (ι : Qbar l ≃+* ℂ) (Γ : Type) [Group Γ] (g : Γ) (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop), D.Classifies ι g admitted → ∀ X : Orb → Finset (Γ →* GL (Fin 3) (Qbar l)), (∀ o, ∀ ρ ∈ X o, admitted ρ) → (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') → (∀ o, ∀ ρ ∈ X o, (ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 q e (z o))) ∧ ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖(ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 q e (z o))‖ := by
  intro q e hq he D Orb _ z hz hσ
  classical
  have := D.fin
  letI : Fintype D.S := Fintype.ofFinite D.S
  let f : Orb → D.S → ℂ := fun o s => (q : ℂ) ^ e * (D.t s - eis3 q e (z o))
  have key : ∀ o s, D.t s ≠ eis3 q e (z o) ∧ IsIntegral ℤ (f o s) ∧
      Real.log ‖f o s‖ ≤ 2 * e * Real.log q + 1 := by
    intro o s
    obtain ⟨k, hk, hzk⟩ := hz o
    exact UpperTheory.eisenstein_trace_difference_log_bound q e k hq he hk (z o) (D.t s) hzk (D.bd s) (D.int s)
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  have hf0 : ∀ o s, f o s ≠ 0 := fun o s =>
    mul_ne_zero (pow_ne_zero _ hq0) (sub_ne_zero.2 (key o s).1)
  obtain ⟨n, hn⟩ := UpperTheory.exists_int_eq_prod_of_galois_permuted_integral (Orb × D.S) (fun p => f p.1 p.2) (fun p => (key p.1 p.2).2.1) (by
    intro σ
    obtain ⟨u, hu⟩ := hσ σ
    obtain ⟨v, hv⟩ := D.conj σ
    refine ⟨u.prodCongr v, fun p => ?_⟩
    simp [f, eis3, hu, hv])
  refine ⟨n, ?_, ?_, ?_⟩
  · intro h
    rw [h, Int.cast_zero] at hn
    exact Finset.prod_ne_zero_iff.2 (fun p _ => hf0 p.1 p.2) hn.symm
  · have h1 : |(n : ℝ)| = ∏ p : Orb × D.S, ‖f p.1 p.2‖ := by
      rw [← norm_prod, ← hn, Complex.norm_intCast]
    rw [h1, Real.log_prod (fun p _ => norm_ne_zero_iff.2 (hf0 p.1 p.2))]
    refine (Finset.sum_le_sum (fun p _ => (key p.1 p.2).2.2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Nat.card_eq_fintype_card, nsmul_eq_mul]
    push_cast
    exact le_rfl
  · intro l _ hl ι Γ _ g admitted hcl X hX hinj
    obtain ⟨cl, hc1, hc2⟩ := hcl
    refine ⟨fun o ρ hρ h => ?_, ?_⟩
    · rw [hc2 ⟨ρ, hX o ρ hρ⟩] at h
      exact (key o _).1 (ι.symm.injective h)
    · have hq1 : ‖(q : Qbar l)‖ = 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
        exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl
      have h2 := UpperTheory.adicNorm_prod_le_prod_of_injective_classes l ι Orb D.S _ f (fun o s => (key o s).2.1) X
        (fun o r => cl ⟨r.1, hX o r.1 r.2⟩)
        (fun o r r' h => Subtype.ext (hinj o _ r.2 _ r'.2 (hc1 _ _ h)))
      rw [← Fintype.prod_prod_type', ← hn, map_intCast] at h2
      refine h2.trans (le_of_eq (Finset.prod_congr rfl fun o _ => ?_))
      rw [← Finset.prod_coe_sort (X o)]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hc2 ⟨r.1, hX o r.1 r.2⟩]
      simp only [f, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, hq1, one_pow, one_mul]
