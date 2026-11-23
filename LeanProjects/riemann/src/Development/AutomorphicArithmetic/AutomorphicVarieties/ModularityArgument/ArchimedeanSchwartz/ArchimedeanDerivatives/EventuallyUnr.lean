import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasInfCharGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Inf

namespace InfinitesimalCharacterOf

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem one_le_term (v : HeightOneSpectrum (𝓞 M)) :
    1 ≤ (v.under (𝓞 K)).asIdeal.ramificationIdx' v.asIdeal * (v.under (𝓞 K)).asIdeal.inertiaDeg' v.asIdeal := by
  haveI := v.isMaximal
  haveI : v.asIdeal.LiesOver (v.under (𝓞 K)).asIdeal := ⟨rfl⟩
  haveI := (v.under (𝓞 K)).isMaximal
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v.asIdeal (v.under (𝓞 K)).ne_bot)
    (Ideal.inertiaDeg'_pos (p := (v.under (𝓞 K)).asIdeal) (P := v.asIdeal)).ne')

private theorem normV_split (h2 : Module.finrank K M = 2) {w w' : HeightOneSpectrum (𝓞 M)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 K) = w.under (𝓞 K)) : normV w = normV (w.under (𝓞 K)) ^ 1 := by
  classical
  have hww : w'.asIdeal ≠ w.asIdeal := fun e => hne (HeightOneSpectrum.ext e)
  have a := one_le_term (K := K) w
  have b := one_le_term (K := K) w'
  rw [hu] at b
  generalize hp : w.under (𝓞 K) = p at a b hu ⊢
  haveI := p.isMaximal
  have mem : ∀ v : HeightOneSpectrum (𝓞 M), v.under (𝓞 K) = p →
      v.asIdeal ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 M) := by
    rintro v rfl
    rw [IsDedekindDomain.mem_primesOverFinset_iff (v.under (𝓞 K)).ne_bot]
    exact ⟨v.isPrime, ⟨rfl⟩⟩
  have hsub : ({w'.asIdeal, w.asIdeal} : Finset (Ideal (𝓞 M))) ⊆
      IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 M) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact mem _ hu
    · exact mem _ hp
  have hle := Finset.sum_le_sum_of_subset (f := fun P => p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P) hsub
  rw [Ideal.sum_ramification_inertia (𝓞 M) K M p.ne_bot, h2, Finset.sum_pair hww] at hle
  have he : p.asIdeal.ramificationIdx' w.asIdeal * p.asIdeal.inertiaDeg' w.asIdeal = 1 := by omega
  have hf : p.asIdeal.inertiaDeg' w.asIdeal = 1 := Nat.dvd_one.1 (Dvd.intro_left _ he)
  haveI : w.asIdeal.LiesOver p.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hp.symm⟩
  have hN := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal p.asIdeal p.isPrime p.ne_bot
  rw [hf] at hN
  exact hN

private theorem eventually_unr (χ : HChar K) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, χ.UnrAt (w.under (𝓞 K)) := by
  rw [Filter.eventually_cofinite]
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
    fun v _ => ?_).subset fun w hw => hw
  haveI := v.isMaximal
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 M) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩

private theorem unr_pow {L : Type} [Field L] [NumberField L] {μ : HChar L} {w : HeightOneSpectrum (𝓞 L)}
    (h : μ.UnrAt w) (k : ℕ) : (μ ^ k).UnrAt w := fun x hx => by
  have e : (μ ^ k).loc w x = μ.loc w x ^ k := MonoidHom.pow_apply μ.1 k _
  rw [e, h x hx, one_pow]

private theorem val_pow {L : Type} [Field L] [NumberField L] (μ : HChar L) (w : HeightOneSpectrum (𝓞 L)) (k : ℕ) :
    (μ ^ k).val w = μ.val w ^ k := MonoidHom.pow_apply μ.1 k _

private theorem indSys_twist [IsTotallyComplex K] [IsTotallyComplex M] (h2 : Module.finrank K M = 2)
    {P : CuspSub K (2 * 2)} {π : CuspSub M 2} (hI : IndSys (CG.mk π).HasSat (CG.mk P).HasSat) (χ : HChar K) (ξ : HChar M)
    (hξ : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), χ.UnrAt (w.under (𝓞 K)) → normV w = normV (w.under (𝓞 K)) ^ f →
      ξ.UnrAt w ∧ ξ.val w = χ.val (w.under (𝓞 K)) ^ f) (k : ℕ) :
    IndSys (CG.mk (π.twist (ξ ^ k))).HasSat (CG.mk (P.twist (χ ^ k))).HasSat := by
  refine (Filter.Eventually.and hI (eventually_unr (M := M) χ)).mono ?_
  rintro w ⟨⟨h1, h3⟩, hu⟩
  simp only [← CG.twist_mk]
  refine ⟨fun w' hne hw' => ?_, fun hq => ?_⟩
  · obtain ⟨B, B', hB, hB', hBP⟩ := h1 w' hne hw'
    obtain ⟨u1, v1⟩ := hξ w 1 hu (normV_split h2 hne hw')
    obtain ⟨u2, v2⟩ := hξ w' 1 (hw' ▸ hu) (normV_split h2 hne.symm hw'.symm)
    refine ⟨_, _, hB.twist (unr_pow u1 k), hB'.twist (unr_pow u2 k), ?_⟩
    have hP := hBP.twist (unr_pow hu k)
    rw [Multiset.map_add] at hP
    rw [val_pow, val_pow, v1, v2, hw', pow_one]
    rwa [val_pow] at hP
  · obtain ⟨B, B', hB, rfl, hBP⟩ := h3 hq
    obtain ⟨u1, v1⟩ := hξ w 2 hu hq
    have e : (ξ ^ k).val w = ((χ ^ k).val (w.under (𝓞 K))) ^ 2 := by
      rw [val_pow, v1, val_pow, ← pow_mul, ← pow_mul, mul_comm]
    refine ⟨_, B'.map (· * (χ ^ k).val (w.under (𝓞 K))), ?_, rfl, ?_⟩
    · have h := hB.twist (unr_pow u1 k)
      rw [e, Multiset.map_map] at h
      rw [Multiset.map_map]
      convert h using 2
      simp [mul_pow]
    · have h := hBP.twist (unr_pow hu k)
      simpa [Multiset.map_add, Multiset.map_map, Function.comp_def] using h

private theorem over_two (h2 : Module.finrank K M = 2) {τ τ' σ : M →+* ℂ} (hne : τ ≠ τ')
    (h1 : τ'.comp (algebraMap K M) = τ.comp (algebraMap K M)) (h3 : σ.comp (algebraMap K M) = τ.comp (algebraMap K M)) :
    σ = τ ∨ σ = τ' := by
  classical
  letI : Algebra K ℂ := (τ.comp (algebraMap K M)).toAlgebra
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos (by omega)
  let a : ∀ ρ : M →+* ℂ, ρ.comp (algebraMap K M) = τ.comp (algebraMap K M) → (M →ₐ[K] ℂ) :=
    fun ρ h => { ρ with commutes' := fun x => RingHom.congr_fun h x }
  have ha : ∀ ρ h ρ' h', a ρ h = a ρ' h' → ρ = ρ' := fun ρ h ρ' h' e =>
    RingHom.ext fun x => DFunLike.congr_fun e x
  have hc := AlgHom.card K M ℂ
  rw [h2] at hc
  by_contra hcon
  push_neg at hcon
  have h3' : ({a σ h3, a τ rfl, a τ' h1} : Finset (M →ₐ[K] ℂ)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a σ h3, a τ rfl, a τ' h1, fun e => hcon.1 (ha _ h3 _ rfl e), fun e => hcon.2 (ha _ h3 _ h1 e),
      fun e => hne (ha _ rfl _ h1 e), rfl⟩
  have := Finset.card_le_univ ({a σ h3, a τ rfl, a τ' h1} : Finset (M →ₐ[K] ℂ))
  omega

private theorem map_sum' {ι : Type} (s : Finset ι) (f : ℂ → ℂ) (g : ι → Multiset ℂ) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := map_sum (Multiset.mapAddMonoidHom f) g s

end InfinitesimalCharacterOf

open InfinitesimalCharacterOf in
theorem infOf : InfOf := by
  intro hSep hUnion hCS hNC K M _ _ _ _ _ _ _ h2 P π hI τ τ' m m' hne hres hm hm'
  classical
  obtain ⟨χ, hχ⟩ := hCS K
  obtain ⟨ξ, hξe, hξv⟩ := hNC K M χ
  have hex : ∀ φ, ∃ μ, P.HasInfChar φ μ := fun φ => (GlobalTheory.ResW.IrrInfChar.main K (2 * 2) φ).1 P
  choose mP hmP using hex
  have hex' : ∀ σ : M →+* ℂ, ∃ μ, π.HasInfChar σ μ := fun σ => (GlobalTheory.ResW.IrrInfChar.main M 2 σ).1 π
  choose m₀ hm₀ using hex'
  let mm : (M →+* ℂ) → Multiset ℂ := fun σ => if σ = τ then m else if σ = τ' then m' else m₀ σ
  have e1 : mm τ = m := if_pos rfl
  have e2 : mm τ' = m' := by
    change (if τ' = τ then m else if τ' = τ' then m' else m₀ τ') = m'
    rw [if_neg hne.symm, if_pos rfl]
  have hmm : ∀ σ, π.HasInfChar σ (mm σ) := by
    intro σ
    by_cases a : σ = τ
    · rw [a, e1]; exact hm
    by_cases b : σ = τ'
    · rw [b, e2]; exact hm'
    · change π.HasInfChar σ (if σ = τ then m else if σ = τ' then m' else m₀ σ)
      rw [if_neg a, if_neg b]
      exact hm₀ σ
  let rs : (M →+* ℂ) → (K →+* ℂ) := fun σ => σ.comp (algebraMap K M)
  let A : (K →+* ℂ) → Multiset ℂ := fun φ => ∑ σ with rs σ = φ, mm σ
  have key : ∀ k : ℕ, ∑ φ, (mP φ).map (· + k * expo χ φ) = ∑ φ, (A φ).map (· + k * expo χ φ) := by
    intro k
    have h := hUnion K M h2 (P.twist (χ ^ k)) (π.twist (ξ ^ k)) (indSys_twist h2 hI χ ξ hξv k)
      (fun φ => (mP φ).map (· + expo (χ ^ k) φ)) (fun σ => (mm σ).map (· + expo (ξ ^ k) σ))
      (fun φ => (hmP φ).twist _) (fun σ => (hmm σ).twist _)
    simp only [GlobalTheory.BCT.TwistDisc.expo_pow, hξe] at h
    rw [h, ← Finset.sum_fiberwise Finset.univ rs]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [map_sum']
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [← (Finset.mem_filter.1 hσ).2]
  have hA := congrFun (hSep (K →+* ℂ) (expo χ) hχ mP A key) (τ.comp (algebraMap K M))
  have hf : (Finset.univ.filter fun σ => rs σ = τ.comp (algebraMap K M)) = {τ, τ'} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun h => over_two h2 hne hres.symm h, ?_⟩
    rintro (rfl | rfl)
    · rfl
    · exact hres.symm
  have hS : A (τ.comp (algebraMap K M)) = m + m' := by
    change ∑ σ with rs σ = τ.comp (algebraMap K M), mm σ = m + m'
    rw [hf, Finset.sum_pair hne, e1, e2]
  rw [← hS, ← hA]
  exact hmP _

end UpperTheory.V.Z.Inf
