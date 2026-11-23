import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusTraceCountBoundOfCmEigensystemCount

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.J

private theorem prime_not_mem_of_other_prime {K : Type} [Field K] [NumberField K] {p l : ℕ} (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime)
    (hl : l.Prime) (hlp : l ≠ p) (hw : (p : 𝓞 K) ∈ w.asIdeal) : (l : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hc : IsCoprime (l : 𝓞 K) (p : 𝓞 K) := Nat.Coprime.cast ((Nat.coprime_primes hl hp).2 hlp)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a h) (w.asIdeal.mul_mem_left b hw)))

private theorem conj_twist_matrix_eq_smul {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]

private theorem is_flag_on_twist {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    {H : Subgroup Γ} {κ : Fin n → ↥H →* kˣ} (h : IsFlagOn r H κ) :
    IsFlagOn (tw r χ) H (fun i => κ i * χ.comp H.subtype) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ⟨fun a b hab => ?_, fun a => ?_⟩⟩
  · have := (hg s).1 a b hab
    show ((g * tw r χ (s : Γ) * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b = 0
    rw [conj_twist_matrix_eq_smul, Matrix.smul_apply]
    exact smul_eq_zero_of_right _ this
  · have := (hg s).2 a
    show ((g * tw r χ (s : Γ) * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a a = ((κ a s * χ (s : Γ) : kˣ) : k)
    rw [conj_twist_matrix_eq_smul, Matrix.smul_apply, smul_eq_mul, this, Units.val_mul]
    exact mul_comm _ _

private theorem flag_at_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G K Ω →* GL (Fin n) (Qbar l)} (j : ℤ)
    {A : ValuationSubring Ω} {κ : Fin n → ↥(Dec (F := K) A) →* (Qbar l)ˣ} (h : FlagAt M m r A κ) :
    FlagAt M (fun i => m i + j) (tw r (cycBar K Ω l ^ j)) A
      (fun i => κ i * (cycBar K Ω l ^ j).comp (Dec (F := K) A).subtype) := by
  obtain ⟨χ, hk, hf, hκ⟩ := h
  refine ⟨χ, hk, is_flag_on_twist _ hf, fun i s hs => ?_⟩
  show κ i s * cycBar K Ω l s ^ j = _
  rw [hκ i s hs, zpow_add, mul_right_comm]

private theorem unlocked_twist_cyclotomic {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G K Ω →* GL (Fin n) (Qbar l)} (j : ℤ)
    (h : Th.Unl l M m r) : Th.Unl l M (fun i => m i + j) (tw r (cycBar K Ω l ^ j)) := by
  intro w hw
  obtain ⟨A, hA, κ, hF, hq⟩ := h w hw
  refine ⟨A, hA, _, flag_at_twist_cyclotomic j hF, fun a b e => hq a b ?_⟩
  rw [mul_right_comm] at e
  exact mul_right_cancel e

private theorem admissible_twist_inverse_cyclotomic {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) (h : Adm3U ι e N ρ) :
    AdmKU ι N ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (tw ρ (cycBar K Ω l)⁻¹) := by
  have hm : ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] = fun i => ![(e : ℤ), 0, -(e : ℤ)] i + (-1) := by
    funext i
    fin_cases i <;> simp <;> ring
  have h1 := UpperTheory.level_twist_cyclotomic_pow K Ω l 3 N _ ρ (-1) h.level
  have h2 := unlocked_twist_cyclotomic (-1) h.unl
  rw [zpow_neg_one] at h1 h2
  rw [hm]
  exact ⟨(UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).1 ρ h.irr, h.aut, { h1 with unl := h2 }⟩

theorem UpperTheory.V.Z.J.tr3U :
    CountKU → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], ∃ c A : ℕ, ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K → ∃ D : TrData (normV w) e, Nat.card D.S ≤ c * (N * (e + 1)) ^ A ∧ ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (normV w) σ → D.Classifies ι σ⁻¹ (Adm3U ι e N) := by
  intro hC K _ _ _
  obtain ⟨c, A, hK⟩ := hC K 3 (by norm_num)
  refine ⟨c * 2 ^ A, A, fun e he N hN p w hp hw hpN hpd => ?_⟩
  have hN' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq : 1 ≤ normV w := by
    rw [← hN']
    exact Nat.one_le_iff_ne_zero.2 fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hqC : ((normV w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : normV w ≠ 0)
  obtain ⟨D, hcard, hcl⟩ := hK ![(e : ℤ) - 1, -1, -(e : ℤ) - 1]
    (by
      refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
      fin_cases i <;> simp <;> omega)
    (by
      intro i
      fin_cases i <;> simp [Fin.rev] <;> ring)
    (e + 1)
    (by
      intro i
      rw [abs_le]
      fin_cases i <;> simp <;> omega)
    N hN p w hp hw hpN hpd
  obtain ⟨T, u, hT⟩ := UpperTheory.traces_from_eigenvalues_rank3 (normV w) e hq D
  refine ⟨T, ?_, fun l _ hl2 hlp Ω _ _ _ ι B hB σ hσ => ?_⟩
  · rw [← Nat.card_congr u, mul_assoc, ← mul_pow]
    refine hcard.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    nlinarith
  · obtain ⟨cl, h1, h2⟩ := hcl l hl2 hlp Ω ι
    refine ⟨fun r => u (cl ⟨_, admissible_twist_inverse_cyclotomic ι e N r.1 r.2⟩), fun r r' H => ?_, fun r => ?_⟩
    · exact (UpperTheory.isIrr_twist_and_repIso_of_twist_repIso _ _ 3 _).2 _ _ (h1 _ _ (u.injective H))
    · have hl := prime_not_mem_of_other_prime w hp (Fact.out : l.Prime) hlp hw
      have e2 := ReciprocityTheory.Gal.cycZ_of_isFrob hl hB hσ
      have e3 : ((cycBar K Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
        change algebraMap ℚ_[l] (Qbar l) (((ReciprocityTheory.Gal.cycZ K Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
        rw [e2]; simp
      have h3 := (UpperTheory.map_trace_eq_sum_roots_of_charpoly_map _ ι.toRingHom _).1 _ ((h2 ⟨_, admissible_twist_inverse_cyclotomic ι e N r.1 r.2⟩ B hB).2 σ hσ)
      rw [tw_val, Matrix.trace_smul, MonoidHom.inv_apply, map_inv (cycBar K Ω l), inv_inv, e3, smul_eq_mul, map_mul,
        map_natCast] at h3
      rw [hT, eq_comm, RingEquiv.symm_apply_eq]
      simp only [mul_inv]
      rw [Multiset.sum_map_mul_left, ← h3, inv_mul_cancel_left₀ hqC]
      rfl
