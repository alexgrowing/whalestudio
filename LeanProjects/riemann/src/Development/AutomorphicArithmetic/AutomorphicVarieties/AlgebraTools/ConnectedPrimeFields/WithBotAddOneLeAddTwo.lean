import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.ImportsVariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CompDim

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem hyper_dim_mono {R : Type} [CommRing R] {I J : Ideal R}
    (h : PrimeSpectrum.zeroLocus (J : Set R) ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  exact Order.krullDim_le_of_strictMono (Set.inclusion h) (fun _ _ hxy => hxy)

private theorem withBot_le_of_add_two (k : ℕ) (d : WithBot ℕ∞) (h : (k : WithBot ℕ∞) + 2 ≤ d + 2) :
    (k : WithBot ℕ∞) ≤ d := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add, le_bot_iff]; exact_mod_cast WithBot.coe_ne_bot (a := ((k + 2 : ℕ) : ℕ∞)))
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact le_top
    | coe d =>
      have h' : ((k + 2 : ℕ) : WithBot ℕ∞) ≤ ((d + 2 : ℕ) : WithBot ℕ∞) := by
        push_cast; exact h
      have h'' : k + 2 ≤ d + 2 := by exact_mod_cast h'
      have h3 : k ≤ d := by omega
      exact_mod_cast h3

private theorem withBot_add_one_le_add_two (d : WithBot ℕ∞) : d + ((1 : ℕ) : WithBot ℕ∞) ≤ d + 2 := by
  gcongr
  exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)

theorem UpperTheory.V.AlgebraTools.Conn.hyper :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R], CohenType R → ∀ (p : Ideal R) (f : R) (k : ℕ), p.IsPrime →
      f ∈ maximalIdeal R → (k : WithBot ℕ∞) + 2 ≤ ringKrullDim (R ⧸ p) → ConnOn (p ⊔ Ideal.span {f}) k := by
  intro R _ _ _ hC p f k hp hf hk I haI hI
  set a : Ideal R := p ⊔ Ideal.span {f} with ha
  have ham : a ≤ maximalIdeal R :=
    sup_le (le_maximalIdeal hp.ne_top) ((Ideal.span_singleton_le_iff_mem _).2 hf)
  have hcomp : ∀ q ∈ a.minimalPrimes, (k : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) := by
    intro q hq
    have h1 := compDim hC p q {f} hp (by simpa using hq)
    rw [Finset.card_singleton] at h1
    exact withBot_le_of_add_two k _ (hk.trans (h1.trans (withBot_add_one_le_add_two _)))
  have hle : ∀ {J K : Ideal R}, J ≤ K → ringKrullDim (R ⧸ K) ≤ ringKrullDim (R ⧸ J) :=
    fun h => hyper_dim_mono (PrimeSpectrum.zeroLocus_anti_mono_ideal h)
  have hmem : ∀ (q : Ideal R) (hq : q ∈ a.minimalPrimes),
      (⟨q, hq.1.1⟩ : PrimeSpectrum R) ∈
        PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R) := by
    intro q hq
    refine ⟨hq.1.2, fun h => ?_⟩
    have h' : I ≤ q := h
    exact absurd ((hcomp q hq).trans (hle h')) (not_le.2 hI)
  refine ⟨?_, ?_⟩
  · obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le ham
    exact ⟨_, hmem q hq⟩
  rw [isPreconnected_closed_iff]
  intro t t' ht ht' hcov hx hy
  by_contra hne
  obtain ⟨b0, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal t).1 ht
  obtain ⟨c0, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal t').1 ht'
  have hdisj : ∀ x : PrimeSpectrum R, a ≤ x.asIdeal → b0 ≤ x.asIdeal → c0 ≤ x.asIdeal →
      I ≤ x.asIdeal := by
    intro x h1 h2 h3
    by_contra h4
    exact hne ⟨x, ⟨h1, h4⟩, h2, h3⟩
  have hmin : ∀ q ∈ a.minimalPrimes, b0 ≤ q ∨ c0 ≤ q := fun q hq => hcov (hmem q hq)
  have hb : ∃ q ∈ a.minimalPrimes, a ⊔ b0 ≤ q := by
    obtain ⟨x, ⟨h1, h2⟩, h3⟩ := hx
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := x.asIdeal) h1
    rcases hmin q hq with h | h
    · exact ⟨q, hq, sup_le hq.1.2 h⟩
    · exact absurd (hdisj x h1 h3 (h.trans hqx)) h2
  have hc : ∃ q ∈ a.minimalPrimes, a ⊔ c0 ≤ q := by
    obtain ⟨x, ⟨h1, h2⟩, h3⟩ := hy
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := x.asIdeal) h1
    rcases hmin q hq with h | h
    · exact absurd (hdisj x h1 (h.trans hqx) h3) h2
    · exact ⟨q, hq, sup_le hq.1.2 h⟩
  set b : Ideal R := a ⊔ b0 with hbdef
  set c : Ideal R := a ⊔ c0 with hcdef
  have hpb : p ≤ b := le_sup_of_le_left le_sup_left
  have hpc : p ≤ c := le_sup_of_le_left le_sup_left
  have hbc : ringKrullDim (R ⧸ (b ⊔ c)) < k := by
    refine lt_of_le_of_lt (hyper_dim_mono fun x hx => ?_) hI
    have hx' : b ⊔ c ≤ x.asIdeal := hx
    exact hdisj x ((le_sup_of_le_left le_sup_left).trans hx')
      ((le_sup_of_le_left le_sup_right).trans hx') ((le_sup_of_le_right le_sup_right).trans hx')
  obtain ⟨q1, hq1, hbq⟩ := hb
  obtain ⟨q2, hq2, hcq⟩ := hc
  have hrad : (b ⊓ c).radical = a.radical := by
    refine le_antisymm ?_ (Ideal.radical_mono (le_inf le_sup_left le_sup_left))
    rw [Ideal.radical_le_radical_iff, ← Ideal.sInf_minimalPrimes]
    refine le_sInf fun q hq => ?_
    rcases hmin q hq with h | h
    · exact inf_le_left.trans (sup_le hq.1.2 h)
    · exact inf_le_right.trans (sup_le hq.1.2 h)
  have hdq : ∀ J : Ideal R, p ≤ J →
      ringKrullDim ((R ⧸ p) ⧸ J.map (Ideal.Quotient.mk p)) = ringKrullDim (R ⧸ J) :=
    fun J h => ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE h)
  have hcm : ∀ J : Ideal R, p ≤ J → (J.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = J := by
    intro J h
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 h]
  have hnt : ∀ J : Ideal R, p ≤ J → J ≠ ⊤ → J.map (Ideal.Quotient.mk p) ≠ ⊤ := by
    intro J h hJ h2
    apply hJ
    rw [← hcm J h, h2, Ideal.comap_top]
  haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hamap : a.map (Ideal.Quotient.mk p) = Ideal.span {Ideal.Quotient.mk p f} := by
    rw [ha, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  have key := one (hC p hp) (Ideal.Quotient.mk p f) (b.map (Ideal.Quotient.mk p))
    (c.map (Ideal.Quotient.mk p)) ?_ ?_
    (hnt b hpb fun h => hq1.1.1.ne_top (top_le_iff.1 (h ▸ hbq)))
    (hnt c hpc fun h => hq2.1.1.ne_top (top_le_iff.1 (h ▸ hcq))) ?_ ?_
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb)] at key
    exact absurd (withBot_le_of_add_two k _ (hk.trans key)) (not_le.2 hbc)
  · rw [← Ideal.span_singleton_le_iff_mem, ← hamap]
    exact le_maximalIdeal (hnt a le_sup_left fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ ham)))
  · apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← hamap, Ideal.comap_radical, Ideal.comap_radical, Ideal.comap_inf, hcm b hpb, hcm c hpc,
      hcm a le_sup_left, hrad]
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb), hdq _ hpb]
    exact hbc.trans_le ((hcomp q1 hq1).trans (hle hbq))
  · rw [← Ideal.map_sup, hdq _ (le_sup_of_le_left hpb), hdq _ hpc]
    exact hbc.trans_le ((hcomp q2 hq2).trans (hle hcq))
