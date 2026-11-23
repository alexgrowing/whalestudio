import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobPlace

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem comap_liesOver {E K : Type} [Field E] [Field K] [NumberField K] (f : 𝓞 E →+* 𝓞 K)
    (la : HeightOneSpectrum (𝓞 K)) :
    (la.asIdeal.comap f).LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := Crude.resCharOf_prime la
  have hP := la.isPrime
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ (la.asIdeal.comap f).under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show f (algebraMap ℤ (𝓞 E) ((resCharOf la : ℕ) : ℤ)) ∈ la.asIdeal
    rw [map_natCast, map_natCast]
    exact Crude.crv_char_mem la
  have hne : (la.asIdeal.comap f).under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ (la.asIdeal.comap f).under ℤ := by rw [h]; trivial
    change f (algebraMap ℤ (𝓞 E) 1) ∈ la.asIdeal at h1
    rwa [map_one, map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem card_under {S : Type} [CommRing S] (p : ℕ) (Q : Ideal S) [h : Q.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem eTau_plOf (D : D7) (z : RPl D.R) :
    ((D.eTau (plOf D z) : D.R.Psi) : D.R.GG) =
      ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
  unfold plOf
  rw [Equiv.apply_symm_apply]
  cases z.1 <;> rfl

theorem inert_ne {N : NumDatum} {l : ℕ} (h : Inert N l) : l ∉ N.H.small ∧ l ≠ N.q ∧ l ≠ N.d := by
  unfold Inert NumDatum.cls primeClass at h
  refine ⟨fun h2 => ?_, fun hq => ?_, fun hd => ?_⟩
  · rw [if_pos h2] at h
    rcases h with h | h <;> cases h
  · rw [if_pos hq] at h
    split_ifs at h <;> rcases h with h | h <;> cases h
  · rw [if_pos hd] at h
    split_ifs at h <;> rcases h with h | h <;> cases h

theorem gal_step (D : D7) (L : SizeData₂ D) (p : ℕ) [Fact p.Prime] (hI : Inert (numOf D L) p)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : RPl D.R) :
    ((D.eTau (plOf D ((numOf D L).pos p z 1)) : D.R.Psi) : D.R.GG) * D.R.cc =
      ((D.eTau (plOf D z) : D.R.Psi) : D.R.GG) *
        D.host.galE σ := by
  obtain ⟨h2, hq, hd⟩ := inert_ne hI
  have hN : ¬ p ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hc : p.Coprime D.host.condN := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  have hC := factClassFrob D.R D.host p hN P σ hσ
  have hH : (D.host.galE σ).2 = D.R.iota ((numOf D L).hP p) := by
    have e1 := (D.host.toHostAx.frob_iff p hc P σ).1 hσ
    have e2 : (numOf D L).hP p = D.R.iotaInv (D.host.art (ZMod.unitOfCoprime p hc)).2 := dif_pos hc
    rw [e2, Formalism.HC.Frame.iota_iotaInv]
    exact congrArg Prod.snd e1
  have hcls : (numOf D L).cls p = D.host.cls p := rfl
  have hpos := eTau_plOf D
    (xor z.1 (decide (D.host.cls p = PrimeClass.signal ∧ Odd 1)), z.2 + 1 • (numOf D L).hP p)
  refine (congrArg (· * D.R.cc) hpos).trans ?_
  rw [eTau_plOf]
  refine Prod.ext ?_ ?_
  · rcases hI with h | h
    · rw [hcls] at h
      have h1 := hC.2.2.1 h
      simp only [Prod.fst_mul, h1, h, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
      cases z.1 <;> simp
    · rw [hcls] at h
      have h1 := hC.2.1.1 h
      simp only [Prod.fst_mul, h1, h, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH]
    rw [Formalism.HC.Frame.iota_add]
    exact congrArg (fun t => D.R.iota z.2 * D.R.iota t) (one_nsmul _)

theorem conj_emb {R : Ranks} (H : Formalism.BasicNotions.Host R) (g g' : R.GG) (σ : H.E ≃ₐ[ℚ] H.E)
    (h : g' * R.cc = g * H.galE σ) (x : H.E) :
    ComplexEmbedding.conjugate (H.emb g') x = H.emb g (σ x) := by
  have hg : ∀ g : R.GG, H.galE (H.sigmaOf g) = g := fun g => MulEquiv.apply_symm_apply _ _
  have he : H.sigmaOf g' * H.conj = H.sigmaOf g * σ := by
    apply H.galE_injective
    rw [H.galE_mul, H.galE_mul, hg, hg, H.galE_conjE, h]
  rw [ComplexEmbedding.conjugate_coe_eq, ← H.conjE_apply (H.emb g') x]
  change H.φ₀ ((H.sigmaOf g' * H.conj) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem frob_place : ∀ (D : D7) (L : SizeData₂ D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (lv : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff lv) (la : HeightOneSpectrum (𝓞 c.F)), Inert (numOf D L) (resCharOf la) → ∀ (z : RPl D.R) (x : 𝓞 D.host.E),
  ∃ y ∈ la.asIdeal, ((y : 𝓞 c.F) : c.F) = embK c (ComplexEmbedding.conjugate (DV.tauEmb D (plOf D ((numOf D L).pos (resCharOf la) z 1)))) x - embK c (DV.tauEmb D (plOf D z)) x ^ resCharOf la := by
  intro D L H lv c la hI z x
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨h2, hq, hd⟩ := inert_ne hI
  let f : 𝓞 D.host.E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (embF c (DV.tauEmb D (plOf D z)))
  haveI := la.isPrime
  haveI := comap_liesOver f la
  have hN : ¬ resCharOf la ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  obtain ⟨σ, hσ⟩ := (D.host.der.frob (resCharOf la) hN (la.asIdeal.comap f)).1
  have hg := gal_step D L (resCharOf la) hI (la.asIdeal.comap f) σ hσ z
  have h1 := hσ x
  rw [card_under (resCharOf la)] at h1
  refine ⟨_, h1, ?_⟩
  rw [map_sub, map_pow]
  push_cast
  congr 1
  apply Subtype.ext
  rw [embK_coe]
  exact (conj_emb D.host _ _ σ hg (x : D.host.E)).symm

end GlobalTheory.FrobPlace
