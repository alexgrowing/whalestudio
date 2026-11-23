import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCompactEmbedded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSup
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_den_chPrime {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    (r : MvPolynomial (Fin m) ℂ) :
    ∃ s : MvPolynomial (Fin m) ℂ, eval t s ≠ 0 ∧ ∀ w : Fin m → ℂ, (∀ h ∈ I, eval w h = 0) →
      eval w s ≠ 0 → eval w r = 0 → ∀ g ∈ Par.chPrime I t r, eval w g = 0 := by
  classical
  have hgen : ∀ g ∈ Par.chPrime I t r, ∃ u : MvPolynomial (Fin m) ℂ, eval t u ≠ 0 ∧
      ∀ w : Fin m → ℂ, (∀ h ∈ I, eval w h = 0) → eval w u ≠ 0 → eval w r = 0 → eval w g = 0 := by
    intro g hg
    have hg' : algebraMap _ (locRing I t) g ∈ Ideal.span {algebraMap _ (locRing I t) r} := hg
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hg'
    obtain ⟨c, b, hb, hcb⟩ := exists_mk_locRing I t a
    have h0 : algebraMap _ (locRing I t) (b * g - c * r) = 0 := by
      rw [map_sub, map_mul, map_mul, ← ha, ← hcb]
      ring
    obtain ⟨s, hs, hsI⟩ := IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero I t h0
    refine ⟨s * b, ?_, fun w hw hsb hr => ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hs hb
    · have h1 := hw _ hsI
      rw [map_mul] at hsb
      rw [map_mul, map_sub, map_mul, map_mul, hr, mul_zero, sub_zero, ← mul_assoc] at h1
      exact (mul_eq_zero.1 h1).resolve_left hsb
  obtain ⟨S, hS⟩ : (Par.chPrime I t r).FG := IsNoetherian.noetherian _
  have hSm : ∀ g ∈ S, g ∈ Par.chPrime I t r := fun g hg => hS ▸ Ideal.subset_span hg
  choose! u hu hu' using fun g (hg : g ∈ S) => hgen g (hSm g hg)
  refine ⟨∏ g ∈ S, u g, ?_, fun w hw hs hr g hg => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 hu
  · rw [map_prod] at hs
    have hle : Par.chPrime I t r ≤ RingHom.ker (eval w) := by
      rw [← hS, Ideal.span_le]
      intro f hf
      exact hu' f hf w hw (Finset.prod_ne_zero_iff.1 hs f hf) hr
    exact hle hg

theorem zero_iff {P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hQ : IsMultiHomogIdeal Q)
    (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (∀ f ∈ Q, eval (rep x) f = 0) ↔ ∀ h ∈ ideal Q p, eval (coord P p x) h = 0 := by
  have hiff := mem_conePts_iff_chartIdeal hQ p (rep x) hx
  constructor
  · intro h
    exact renPt_zero _ _ (hiff.1 ⟨(rep_mem x).1, h⟩)
  · intro h
    have h2 : rep x ∈ conePts Q := hiff.2 fun f hf => by
      rw [← eval_renC]
      exact h _ (Ideal.mem_map_of_mem _ hf)
    exact h2.2

theorem continuousOn_coord {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) :
    ContinuousOn (coord P p) (src P p) :=
  continuousOn_iff_continuous_domRestrict.2 (Top.isEmbedding_coord p).continuous

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.comp_eq_near : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (x : SncRes.Pts P) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (σ : Fin e → Option (Fin (SncRes.rc P D))), IsMultiHomogIdeal P → IsMultiHomogIdeal D → x ∈ SncRes.src P p → (∀ h ∈ (SncRes.ideal P p), eval (SncRes.coord P p x) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (SncRes.coord P p x)) → ringKrullDim (locRing (SncRes.ideal P p) (SncRes.coord P p x)) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x)) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x))) (ptIdeal (SncRes.coord P p x)) → (∀ l, σ l = none ↔ l ∉ Jf) → (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)) → (∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0) → ∃ l ∈ Jf, σ l = some k) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∀ k, SncRes.comp P D k ∩ O = {x' ∈ O | ∃ l, σ l = some k ∧ eval (SncRes.coord P p x') (r l) = 0} := by
  intro K _ ι _ P D e p x r Jf σ hP hD hx _ _ _ _ _ hch hout
  classical
  have hQ : ∀ k, IsMultiHomogIdeal (SncRes.compIdeal P D k) := fun k =>
    MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup K ι P D hP hD _ (SncRes.compIdeal_mem D k)
  choose s hst hsw using fun l =>
    SncRes.NearComp.exists_den_chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)
  have hg : ∀ k, ∃ g, eval (SncRes.coord P p x) g ≠ 0 ∧
      ((∃ l, σ l = some k) ∨ g ∈ SncRes.ideal (SncRes.compIdeal P D k) p) := by
    intro k
    by_cases hk : ∃ l, σ l = some k
    · exact ⟨1, by simp, Or.inl hk⟩
    · have hnz : ¬ ∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0 := fun h => by
        obtain ⟨l, -, hl⟩ := hout k h
        exact hk ⟨l, hl⟩
      have hn : ¬ ∀ h ∈ SncRes.ideal (SncRes.compIdeal P D k) p,
          eval (SncRes.coord P p x) h = 0 :=
        fun h => hnz ((SncRes.NearComp.zero_iff (hQ k) p x hx).2 h)
      push Not at hn
      obtain ⟨g, hg, hgt⟩ := hn
      exact ⟨g, hgt, Or.inr hg⟩
  choose g hgt hgk using hg
  let F := (∏ l, s l) * ∏ k, g k
  have hFw : ∀ w, eval w F ≠ 0 ↔ (∀ l, eval w (s l) ≠ 0) ∧ ∀ k, eval w (g k) ≠ 0 := by
    intro w
    simp only [F, map_mul, map_prod, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, not_exists]
  refine ⟨SncRes.src P p ∩ SncRes.coord P p ⁻¹' {w | eval w F ≠ 0}, ?_,
    ⟨hx, (hFw _).2 ⟨hst, hgt⟩⟩, Set.inter_subset_left, fun k => ?_⟩
  · exact (SncRes.NearComp.continuousOn_coord p).isOpen_inter_preimage (SncRes.Top.isOpen_alt_bis p)
      (isOpen_ne_fun (MvPolynomial.continuous_eval F) continuous_const)
  · ext x'
    constructor
    · rintro ⟨hc, ho⟩
      refine ⟨ho, ?_⟩
      have hz := (SncRes.NearComp.zero_iff (hQ k) p x' ho.1).1 hc
      rcases hgk k with ⟨l, hl⟩ | hk
      · refine ⟨l, hl, hz _ ?_⟩
        rw [hch l k hl]
        exact Ideal.mem_comap.2 (Ideal.subset_span rfl)
      · exact absurd (hz _ hk) (((hFw _).1 ho.2).2 k)
    · rintro ⟨ho, l, hl, hr⟩
      refine ⟨?_, ho⟩
      refine (SncRes.NearComp.zero_iff (hQ k) p x' ho.1).2 ?_
      rw [hch l k hl]
      exact hsw l _ ((SncRes.NearComp.zero_iff hP p x' ho.1).1 (SncRes.rep_mem x').2)
        (((hFw _).1 ho.2).1 l) hr
