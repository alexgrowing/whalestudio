import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem placesOk_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), q0.Prime → (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≡ 1 [MOD H.QS * H.q * H.d]) → (∀ k, q0 ≠ H.g k) → q0 ≠ H.pde → q0 ≠ H.pde' → OverP H q0 w0 → PlacesOk H q0 w0 ∧ 5 ≤ q0 := by
  intro R H q0 w0 hq hmod hg hp hp' hw
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := by
    intro p h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    exacts [H.g_prime 0, H.g_prime 1, H.pde_prime, H.pde'_prime, hq]
  have h4 : (4 : ℕ) ∣ H.QS * H.q * H.d := (by norm_num : 4 ∣ 16).trans H.sixteen_dvd_condN
  have h5 : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], 5 ≤ p := by
    intro p h
    have h1 : p % 4 = 1 % 4 := (hmod p h).of_dvd h4
    have h2 := (hprime p h).two_le
    omega
  refine ⟨⟨hw, ?_, fun p h => ?_⟩, h5 q0 (by simp)⟩
  · have a1 := H.g_ne
    have a2 := H.pde_ne
    have a3 := H.pde_ne_g 0
    have a4 := H.pde_ne_g 1
    have a5 := hg 0
    have a6 := hg 1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    omega
  · have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p (hprime p h) (hmod p h)
    have := h5 p h
    refine ⟨hprime p h, by omega, ?_, fun P hP => (GlobalTheory.Mem.Chr.splitsC_main R H p (hprime p h) hs P hP).1⟩
    exact GlobalTheory.SplitEmbSep.not_dvd_discr_of_split (hprime p h) _
      ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver (hprime p h)).symm.trans hs)

end GlobalTheory.LamTie
