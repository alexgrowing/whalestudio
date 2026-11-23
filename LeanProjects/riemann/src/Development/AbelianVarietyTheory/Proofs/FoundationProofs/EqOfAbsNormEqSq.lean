import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadPlaces

theorem conjSrc_one {M : Type} [Field M] [NumberField M] (w : HeightOneSpectrum (𝓞 M)) :
    GlobalTheory.CuspRep.conjSrc (1 : M ≃+* M) w = w := by
  refine (GlobalTheory.CuspRep.eq_conjSrc ?_).symm
  rw [GlobalTheory.Mem.Chr.conjPl_iff_comap]
  ext x
  rfl

theorem eq_of_absNorm_eq_sq {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (h2 : Module.finrank K M = 2) (w w' : HeightOneSpectrum (𝓞 M))
    (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2)
    (hw' : w'.under (𝓞 K) = w.under (𝓞 K)) : w' = w := by
  set v := w.under (𝓞 K) with hv
  have : v.asIdeal.IsPrime := v.isPrime
  have : w.asIdeal.IsPrime := w.isPrime
  have hl : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  have hpow := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
  have hf : w.asIdeal.inertiaDeg (𝓞 K) = 2 :=
    Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v) (hpow.trans hN)
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) (M ≃ₐ[K] M)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (M ≃ₐ[K] M), hf, IsGalois.card_aut_eq_finrank, h2,
    ← mul_assoc] at hfund
  have h1 : (v.asIdeal.primesOver (𝓞 M)).ncard * v.asIdeal.ramificationIdxIn (𝓞 M) = 1 := by omega
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.1 (Nat.eq_one_of_mul_eq_one_right h1)
  have a : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨w.isPrime, hl⟩
  have b : w'.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨w'.isPrime, hl'⟩
  rw [hP, Set.mem_singleton_iff] at a b
  exact HeightOneSpectrum.ext (b.trans a.symm)

theorem main : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], Module.finrank K M = 2 → ∀ (s : M ≃ₐ[K] M), s ≠ 1 → ∀ w : HeightOneSpectrum (𝓞 M), (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w ∨ w' = GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) ∧ (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w).under (𝓞 K) = w.under (𝓞 K) ∧ GlobalTheory.CuspRep.conjSrc ((1 : M ≃ₐ[K] M) : M ≃+* M) w = w ∧ (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 → GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w = w) := by
  intro K M _ _ _ _ _ _ h2 s hs w
  have hu : GlobalTheory.Mem.Chr.ConjPl s.toRingEquiv (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) w :=
    GlobalTheory.CuspRep.conjPl_conjSrc (s : M ≃+* M) w
  have hunder : (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w).under (𝓞 K) = w.under (𝓞 K) :=
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl s h2 hs (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) w).2 (Or.inr hu)).symm
  refine ⟨fun w' hw' => ?_, hunder, conjSrc_one w, fun hN => eq_of_absNorm_eq_sq h2 w _ hN hunder⟩
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl s h2 hs (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) w').1
      (hw'.trans hunder.symm) with h | h
  · exact Or.inr h
  · exact Or.inl ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ _).unique h hu)

end GlobalTheory.QuadPlaces
