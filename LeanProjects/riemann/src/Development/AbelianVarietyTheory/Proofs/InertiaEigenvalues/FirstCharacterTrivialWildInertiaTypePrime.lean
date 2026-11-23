import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypes

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChiTame

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1 := by
  intro D i k v hne s hs
  have hwg : D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) := D.naut.plGw_over k v
  have hpl := D.nd.plOm.2 (D.naut.plGw k v)
  have hI : s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) := GlobalTheory.TameGenPowers.wild_mem_Ine hs
  have hcop : (D.nd.l i).Coprime (D.host.g k) :=
    (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 hne
  have hgv : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
    have h2 := (hpl _).2 hwg
    simpa using h2
  have hvl : D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
    intro hl
    have h2 := (hpl _).2 hl
    exact GlobalTheory.WildKill.not_lt_one_of_coprime _ hcop hgv (by simpa using h2)
  have hl : D.ntw.l (D.ntw.twOf i) = D.nd.l i := D.ntw.twOf_l i
  have ht := D.ntw.twistCharacterFamily_tame (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) k _ hwg (by rw [hl]; exact hvl)
    _ hpl s hI
  obtain ⟨n, hn⟩ := D.ntw.psiL_ord i s
  have h1 : ((Units.map (D.ntw.twist₂ i).toMonoidHom).comp
      (D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i))) s ^ (D.host.g k - 1) = 1 := by
    rw [MonoidHom.comp_apply, ← map_pow, ht, map_one]
  have hpow : D.nd.chi i 1 s ^ ((D.host.g k - 1) * D.nd.l i ^ n) = 1 := by
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, mul_pow, pow_mul, h1, one_pow, one_mul, pow_mul', hn, one_pow]
  have := D.nd.trO i
  exact GlobalTheory.WildSetSQ.char_eq_one_of_wild (D.nd.plOm.1 (D.naut.plGw k v)) (D.nd.O_adic i) (D.nd.chi i 1)
    (D.nd.chi_cont i 1) s hs _
    (GlobalTheory.WildKill.not_lt_one_of_coprime _
      (Nat.Coprime.mul (GlobalTheory.WildSetSQ.coprime_pred _ (D.host.g_prime k).one_lt.le)
        (Nat.Coprime.pow_left n hcop)) hgv) hpow

end GlobalTheory.ChiTame
