import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturatedStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSupStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRingAltBis

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ideal_mono {S S' : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h : S ≤ S') (p : (k : K) → ι k) :
    SncRes.ideal S p ≤ SncRes.ideal S' p :=
  Ideal.map_mono (sup_le_sup_right h _)

theorem renR_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
    {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : renR (Σ k, ι k) g ∈ SncRes.ideal S p :=
  Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hg)

theorem renR_X_sub_one_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (k : K) :
    renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ SncRes.ideal S p :=
  Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))

theorem renR_sub_deh_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    renR (Σ k, ι k) f - bind₁ (SncRes.lift p) f ∈ SncRes.ideal S p := by
  classical
  have key : (Ideal.Quotient.mk (SncRes.ideal S p)).comp
        (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) =
      (Ideal.Quotient.mk (SncRes.ideal S p)).comp
        (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [renameEquiv_apply]
    · rintro ⟨k, i⟩
      by_cases h : i = p k
      · subst h
        have h1 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
        have h2 := renR_X_sub_one_mem S p k
        rw [map_sub, map_one] at h2
        simpa [h1] using Ideal.Quotient.eq.2 h2
      · have h1 : SncRes.lift p ⟨k, i⟩ = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
          simp [SncRes.lift, h]
        simp [h1, renameEquiv_apply]
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun key f)

theorem deh_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
    {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : bind₁ (SncRes.lift p) g ∈ SncRes.ideal S p := by
  have h := (SncRes.ideal S p).sub_mem (renR_mem p hg) (renR_sub_deh_mem S p g)
  simpa using h

theorem exists_compIdeal_eq {P D Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hQ : Q ∈ (P ⊔ D).minimalPrimes) : ∃ k, SncRes.compIdeal P D k = Q := by
  refine ⟨(SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin
    ⟨Q, (Set.Finite.mem_toFinset _).2 hQ⟩, ?_⟩
  simp [SncRes.compIdeal]

theorem compIdeal_injective (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
    Function.Injective (SncRes.compIdeal P D) := by
  intro a b h
  exact ((SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin).symm.injective (Subtype.ext h)

theorem exists_minimal_below {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
    {𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)} (h𝔮 : 𝔮.IsPrime)
    (hD : SncRes.ideal (P ⊔ D) p ≤ 𝔮) :
    ∃ Q ∈ (P ⊔ D).minimalPrimes,
      (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) ∧ SncRes.ideal Q p ≤ 𝔮 := by
  classical
  have hle : P ⊔ D ≤ 𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _) :=
    fun g hg => hD (deh_mem p hg)
  haveI : (𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _)).IsPrime :=
    Ideal.comap_isPrime _ _
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
  refine ⟨Q, hQ, fun k hX => ?_, ?_⟩
  · have h1 : bind₁ (SncRes.lift p) (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮 := hQle hX
    have h2 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
    rw [bind₁_X_right, h2] at h1
    exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · refine Ideal.map_le_iff_le_comap.2 (sup_le ?_ ?_)
    · intro f hf
      have h1 : bind₁ (SncRes.lift p) f ∈ 𝔮 := hQle hf
      have h2 := 𝔮.add_mem (hD (renR_sub_deh_mem (P ⊔ D) p f)) h1
      simpa using h2
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact hD (renR_X_sub_one_mem (P ⊔ D) p k)

theorem components_of_params : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ σ : Fin e → Option (Fin (SncRes.rc P D)), Set.InjOn σ Jf ∧ (∀ l, σ l = none ↔ l ∉ Jf) ∧ (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧ ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k) ∧ ∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval z g = 0) → ∃ l ∈ Jf, σ l = some k := by
  intro K _ ι _ P D e p z r Jf hP hD hz hzp hI reg dim span hprim
  have hIDc : SncRes.ideal P p ≤ SncRes.ideal (P ⊔ D) p := ideal_mono le_sup_left p
  have pr := GlobalTheory.T.regular_system_of_parameters_local_ring_alt _ e (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) (renPt (affCoord p z)) r Jf
    hIDc hI reg dim span hprim
  have hmin := GlobalTheory.T.minimal_primes_of_multihomog_sup K ι P D hP hD
  have step : ∀ l (_ : l ∈ Jf), ∃ k, SncRes.ideal (SncRes.compIdeal P D k) p =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧
      ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
    intro l hl
    obtain ⟨hpr, hIq, hqt, hDq, hrl, hsep, hmn⟩ := pr l hl
    obtain ⟨Q, hQ, hX, hQle⟩ := exists_minimal_below p hpr hDq
    have hQh := hmin Q hQ
    have hQp : Q.IsPrime := hQ.1.1
    obtain ⟨hQpr, -⟩ := GlobalTheory.T.affine_chart_ideal_prime_and_saturated K ι Q p hQh hQp hX
    have hDQ : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal Q p := ideal_mono hQ.1.2 p
    have hIQ := hIDc.trans hDQ
    obtain ⟨j, hj, hrj⟩ := (hprim _ hQpr hIQ (hQle.trans hqt)).1 hDQ
    have hjl : j = l := by
      by_contra hne
      exact hsep j hj hne (hQle hrj)
    subst hjl
    obtain ⟨k, rfl⟩ := exists_compIdeal_eq hQ
    exact ⟨k, le_antisymm hQle (hmn _ hQpr hIQ (hQle.trans hqt) hrj), hX⟩
  classical
  choose κ hκ using step
  have hσ : ∀ l k, (if h : l ∈ Jf then some (κ l h) else none) = some k →
      ∃ h : l ∈ Jf, κ l h = k := by
    intro l k h
    by_cases hl : l ∈ Jf
    · rw [dif_pos hl] at h
      exact ⟨hl, Option.some.inj h⟩
    · rw [dif_neg hl] at h
      cases h
  refine ⟨fun l => if h : l ∈ Jf then some (κ l h) else none, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a ∈ Jf := ha
    have hb' : b ∈ Jf := hb
    simp only [dif_pos ha', dif_pos hb'] at hab
    have hk := Option.some.inj hab
    have heq : SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r a) =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r b) := by
      rw [← (hκ a ha').1, ← (hκ b hb').1, hk]
    by_contra hne
    obtain ⟨-, -, -, -, -, hsep, -⟩ := pr a ha'
    obtain ⟨-, -, -, -, hrb, -, -⟩ := pr b hb'
    exact hsep b hb' (Ne.symm hne) (heq ▸ hrb)
  · intro l
    by_cases hl : l ∈ Jf <;> simp [hl]
  · intro l k h
    obtain ⟨hl, rfl⟩ := hσ l k h
    exact hκ l hl
  · intro k hk
    have hQk := SncRes.compIdeal_mem (P := P) D k
    have hkh := hmin _ hQk
    have hkp : (SncRes.compIdeal P D k).IsPrime := hQk.1.1
    have hX : ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
      intro k' hx
      exact hzp k' (by simpa using hk _ hx)
    obtain ⟨hkpr, hdict⟩ := GlobalTheory.T.affine_chart_ideal_prime_and_saturated K ι _ p hkh hkp hX
    have hzc : z ∈ conePts (SncRes.compIdeal P D k) := ⟨hz.1, hk⟩
    have hpt : SncRes.ideal (SncRes.compIdeal P D k) p ≤ ptIdeal (renPt (affCoord p z)) := by
      intro h hh
      exact renPt_zero _ _ ((mem_conePts_iff_chartIdeal hkh p z hzp).1 hzc) h hh
    have hDk : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal (SncRes.compIdeal P D k) p :=
      ideal_mono hQk.1.2 p
    have hIk := hIDc.trans hDk
    obtain ⟨l, hl, hrl⟩ := (hprim _ hkpr hIk hpt).1 hDk
    obtain ⟨-, -, -, -, -, -, hmn⟩ := pr l hl
    have hle := hmn _ hkpr hIk hpt hrl
    rw [← (hκ l hl).1] at hle
    have hQ0 := SncRes.compIdeal_mem (P := P) D (κ l hl)
    obtain ⟨S, hS, hSeq⟩ := hmin _ hQ0
    have hsub : SncRes.compIdeal P D (κ l hl) ≤ SncRes.compIdeal P D k := by
      rw [hSeq, Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfQ : f ∈ SncRes.compIdeal P D (κ l hl) := hSeq ▸ Ideal.subset_span hf
      exact (hdict f a ha).1 (hle (deh_mem p hfQ))
    have heq : SncRes.compIdeal P D (κ l hl) = SncRes.compIdeal P D k :=
      le_antisymm hsub (hQk.2 ⟨hQ0.1.1, hQ0.1.2⟩ hsub)
    refine ⟨l, hl, ?_⟩
    beta_reduce
    rw [dif_pos hl, compIdeal_injective P D heq]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
