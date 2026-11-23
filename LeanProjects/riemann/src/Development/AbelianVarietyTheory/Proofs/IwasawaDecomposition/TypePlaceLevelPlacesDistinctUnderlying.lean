import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelTypePlace

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom R)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    {q : ℕ} (hc : Nat.card (𝓞 E ⧸ PP.asIdeal) = q) (hq0 : q ≠ 0) : (q : 𝓞 E) ∈ PP.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem offPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w ∈ L.Pg → (∀ PP ∈ L.Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) ∧ (∀ PP ∈ L.Q t, ¬ NG.OverPl PP s.v) ∧ s.w ∉ L.Q t ∧ (L.xiH t).UnrAt s.w := by
  intro D T L μ0 hL hPg t s hs

  have hA : ∀ PP : Pl D.host.E, NG.OverPl PP s.v → ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ s.w.asIdeal →
      (p : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hov p hp
    have h1 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← s.w_under, Ideal.mem_comap, map_natCast]; exact hp
    rw [← hov, Ideal.mem_comap, map_natCast] at h1; exact h1
  have hgne : ∀ k k' : Fin 2, k ≠ k' → D.host.g k ≠ D.host.g k' := by
    intro k k' h
    fin_cases k <;> fin_cases k' <;> first | exact absurd rfl h | exact D.host.g_ne | exact D.host.g_ne.symm
  obtain ⟨k, v, hkv⟩ := (hPg s.w).1 hs
  have hgk : (D.host.g k : 𝓞 D.host.E) ∈ s.w.asIdeal := by rw [hkv]; exact D.naut.plGw_over k v

  have hQ : ∀ PP ∈ L.Q t, (D.host.g k : 𝓞 D.host.E) ∈ PP.asIdeal → False := by
    intro PP hP hg
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP hP).1
    exact not_two_primes PP.asIdeal (D.host.g_prime k) hq (hqg k).symm hg
      (natCast_mem_of_card PP hcard hq.ne_zero)
  have h3 : s.w ∉ L.Q t := fun h => hQ s.w h hgk
  refine ⟨?_, fun PP hP hov => hQ PP hP (hA PP hov _ hgk), h3, ?_⟩
  · intro PP hP hne hov
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s PP hov with e | hc
    · exact hne e.symm
    obtain ⟨k', v', hkv'⟩ := (hPg PP).1 hP
    have hk : k' = k := by
      by_contra hk
      have h1 : (D.host.g k' : 𝓞 D.host.E) ∈ PP.asIdeal := by rw [hkv']; exact D.naut.plGw_over k' v'
      exact not_two_primes PP.asIdeal (D.host.g_prime k') (D.host.g_prime k) (hgne k' k hk) h1
        (hA PP hov _ hgk)
    subst hk
    rw [hkv, hkv'] at hc
    exact D.naut.plGw_nconj k' v' v hc
  · by_contra hn
    rcases (hL.Q_ram t s.w).1 hn with h | ⟨PP', hP', hc⟩
    · exact h3 h
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP' hP').1
    obtain ⟨c', hc', hcq⟩ := hc _ (natCast_mem_of_card PP' hcard hq.ne_zero)
    have hq' : (q : 𝓞 D.host.E) = c' := by
      apply RingOfIntegers.ext
      rw [hcq]; simp
    exact not_two_primes s.w.asIdeal (D.host.g_prime k) hq (hqg k).symm hgk (hq' ▸ hc')

end GlobalTheory.LevelTypePlace
