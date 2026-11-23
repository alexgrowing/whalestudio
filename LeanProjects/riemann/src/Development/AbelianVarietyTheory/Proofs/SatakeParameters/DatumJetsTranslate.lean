import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJetsOfTranslateJets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousToZModComp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespond
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets.Transl

open GlobalTheory.LiftTypePrime GlobalTheory.MomT.PtMoments

theorem exists_denom {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module (𝓞 E) W] {p : ℕ} (hp : p.Prime)
    {M M' : Submodule (𝓞 E) W} (hM : M.FG)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → M ≤ localization₂ P.asIdeal M') :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ M, (s : 𝓞 E) • x ∈ M' := by
  have key : ∀ x : W, ∃ s : ℕ, Nat.Coprime s p ∧ (x ∈ M → (s : 𝓞 E) • x ∈ M') := fun x => by
    by_cases hx : x ∈ M
    swap
    · exact ⟨1, by simp, fun h => absurd h hx⟩
    by_contra hn
    let I : Ideal (𝓞 E) := M'.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
    have hI : I.comap (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(p : ℤ)} := fun z hz => by
      rw [Ideal.mem_span_singleton, Int.natCast_dvd]
      by_contra hz'
      refine hn ⟨z.natAbs, ((Nat.Prime.coprime_iff_not_dvd hp).2 hz').symm, fun _ => ?_⟩
      have hz1 : (z : 𝓞 E) • x ∈ M' := hz
      rcases Int.natAbs_eq z with h1 | h1
      · rw [h1, Int.cast_natCast] at hz1; exact hz1
      · rw [h1, Int.cast_neg, Int.cast_natCast, neg_smul, neg_mem_iff] at hz1; exact hz1
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)}) I hI
    have hpQ : (p : 𝓞 E) ∈ Q := by
      have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := hQc ▸ Ideal.mem_span_singleton_self _
      simpa using this
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hp.ne_zero (by simpa using hpQ)
    obtain ⟨c, hc, hcx⟩ : ∃ c : 𝓞 E, c ∉ Q ∧ c • x ∈ M' := h ⟨Q, hQp, hQ0⟩ hpQ hx
    exact hc (hQ hcx)
  choose f hf hfx using key
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∏ x ∈ S, f x, Nat.Coprime.prod_left fun x _ => hf x, fun x hx => ?_⟩
  refine (Submodule.span_le (p := M'.comap (((∏ x ∈ S, f x : ℕ) : 𝓞 E) • LinearMap.id))).2 (fun y hy => ?_) hx
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hy)
  change ((∏ x ∈ S, f x : ℕ) : 𝓞 E) • y ∈ M'
  rw [hc, mul_comm, Nat.cast_mul, mul_smul]
  exact M'.smul_mem _ (hfx y (Submodule.subset_span hy))

theorem stdLat_fg (E : Type) [Field E] (n : ℕ) : (Formalism.L2.Col.stdLat E n).FG :=
  Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _

theorem stdAt_of_stdOver (D : D7) {p : ℕ} (hp : p.Prime) {n : ℕ} {N : Submodule (𝓞 D.host.E) (Sp D.host.E n)} (hN : N.FG)
    (h : StdOver p N) : StdAt D p ((recSeam D).lat N) := by
  obtain ⟨s, hs, h1⟩ := exists_denom hp hN (M' := Formalism.L2.Col.stdLat D.host.E n) fun P hP => (le_locP _ _).trans (h P hP).le
  obtain ⟨t, ht, h2⟩ := exists_denom hp (stdLat_fg D.host.E n) (M' := N) fun P hP => (le_locP _ _).trans (h P hP).ge
  have hl : ∀ x, x ∈ (recSeam D).lat N ↔ x ∈ N := fun x => GlobalTheory.SeamTransport.mem_lat (recSeam D) N x
  refine ⟨Formalism.L2.Col.stdLat D.host.E n, fun x => ?_, s * t, hs.mul_left ht, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun hy => ⟨⟨_, hy⟩, rfl⟩⟩
  · have := h1 x ((hl x).1 hx)
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [mul_comm, mul_smul]
    exact nsmul_mem this _
  · have := h2 x hx
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [hl, mul_smul]
    exact nsmul_mem this _

variable {D : D7} {a b : ℕ}

theorem applyAt0_monomial (cD : D.what₂.Tau → ℂ) (G : TaylorLogMetric.VC D a b → ℂ) (m : TaylorLogMetric.Mono D a b) :
    GL3Theta.applyAt0 D (inLetters D cD (MvPolynomial.monomial m 1)) G =
      (m.prod fun k n => cD k.1 ^ n) * ((m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G m) := by
  classical
  have h : inLetters D cD (MvPolynomial.monomial m (1 : ℂ)) = MvPolynomial.monomial m (m.prod fun k n => cD k.1 ^ n) := by
    rw [inLetters, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
    simp only [mul_pow, Finsupp.prod_mul, map_one, one_mul, map_finsuppProd, map_pow]
  rw [h, GL3Theta.applyAt0, Finset.sum_subset MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl, mul_assoc]
  intro x _ hx
  rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul, zero_mul]

end GlobalTheory.DatumJets.Transl
