import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Eta

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => maximalRealSubfield K

theorem cases (g : K ≃ₐ[K⁺] K) : g = 1 ∨ g = IsCMField.complexConj K := by
  classical
  by_contra hne
  push_neg at hne
  have h2 : Nat.card (K ≃ₐ[K⁺] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  haveI : Fintype (K ≃ₐ[K⁺] K) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h2
  have h3 : ({1, IsCMField.complexConj K, g} : Finset (K ≃ₐ[K⁺] K)).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, IsCMField.complexConj K, g,
      (IsCMField.complexConj_ne_one K).symm, hne.1.symm, hne.2.symm, rfl⟩
  have h4 := Finset.card_le_univ ({1, IsCMField.complexConj K, g} : Finset (K ≃ₐ[K⁺] K))
  omega

theorem card_gal : Nat.card (K ≃ₐ[K⁺] K) = 2 := by
  rw [IsGalois.card_aut_eq_finrank]
  exact Algebra.IsQuadraticExtension.finrank_eq_two _ _

instance isGaloisGroup : IsGaloisGroup (K ≃ₐ[K⁺] K) (𝓞 K⁺) (𝓞 K) :=
  IsGaloisGroup.of_isFractionRing _ _ _ K⁺ K

theorem split_or_inert
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (𝔭 : Ideal (𝓞 K⁺)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    (primesOver 𝔭 (𝓞 K)).ncard = 2 ∨
      ((primesOver 𝔭 (𝓞 K)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 K) = 2) := by
  classical
  have hmax : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭
  obtain ⟨P, hPp, hPl⟩ : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P.LiesOver 𝔭 := by
    first
    | exact Ideal.nonempty_primesOver (S := 𝓞 K) 𝔭
    | (obtain ⟨Q, hQ⟩ := Ideal.nonempty_primesOver (S := 𝓞 K) 𝔭; exact ⟨Q, hQ.1, hQ.2⟩)
    | (obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭
          (S := 𝓞 K) (by
            rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective _ _)]
            exact bot_le)
       exact ⟨Q, hQm.isPrime, ⟨hQ.symm⟩⟩)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭 P
  have hin : P.inertia (K ≃ₐ[K⁺] K) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rcases cases K g with h | h
    · exact h
    · exfalso
      subst h
      exact hunr P hPp hP0 (fun x => hg x)
  have h1 := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := K ≃ₐ[K⁺] K) 𝔭 P
  rw [hin, Subgroup.card_bot, mul_one, card_gal K] at h1
  rw [Ideal.inertiaDegIn_eq_inertiaDeg 𝔭 P (K ≃ₐ[K⁺] K)]
  have hfpos : 0 < P.inertiaDeg (𝓞 K⁺) := Ideal.inertiaDeg_pos P (𝓞 K⁺)
  generalize (𝔭.primesOver (𝓞 K)).ncard = n at h1 ⊢
  generalize P.inertiaDeg (𝓞 K⁺) = f at h1 hfpos ⊢
  have hn : n ≤ 2 := by nlinarith
  interval_cases n
  · omega
  · right; exact ⟨rfl, by omega⟩
  · left; rfl

theorem ncard_eq_two_iff
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥) :
    (primesOver (P.under (𝓞 K⁺)) (𝓞 K)).ncard = 2 ↔ IsCMField.complexConj K • P ≠ P := by
  classical
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (P.under (𝓞 K⁺)) (𝓞 K) (K ≃ₐ[K⁺] K)
  have h2 := Ideal.card_stabilizer_eq (G := K ≃ₐ[K⁺] K) (P.under (𝓞 K⁺)) P
  rw [← h2, card_gal K] at h1
  have hmem : ∀ g : K ≃ₐ[K⁺] K, g ∈ MulAction.stabilizer (K ≃ₐ[K⁺] K) P ↔ g • P = P :=
    fun g => MulAction.mem_stabilizer_iff
  constructor
  · intro h hcP
    have hne : MulAction.stabilizer (K ≃ₐ[K⁺] K) P ≠ ⊥ := by
      intro hb
      have hc : IsCMField.complexConj K ∈ MulAction.stabilizer (K ≃ₐ[K⁺] K) P := (hmem _).mpr hcP
      rw [hb, Subgroup.mem_bot] at hc
      exact IsCMField.complexConj_ne_one K hc
    have h3 : Nat.card (MulAction.stabilizer (K ≃ₐ[K⁺] K) P) ≠ 1 :=
      fun h' => hne (Subgroup.card_eq_one.mp h')
    rw [h] at h1
    omega
  · intro hcP
    have hb : MulAction.stabilizer (K ≃ₐ[K⁺] K) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      rcases cases K g with hg1 | hg1
      · exact hg1
      · exfalso
        apply hcP
        rw [← hg1]
        exact (hmem g).mp hg
    rw [hb, Subgroup.card_bot, mul_one] at h1
    exact h1

end CM

section Host

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

def cQ (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b :=
  haveI := isCMField_hostE hqd h
  (IsCMField.complexConj (hostE ζ a b)).restrictScalars ℚ

theorem galE_cQ (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    galE e ζ a b (cQ hqd h) = cc e := by
  haveI := isCMField_hostE hqd h
  obtain ⟨-, -, hmul, hbij⟩ := hostGalois e q d hqd L ζ a b h
  obtain ⟨σ0, hσ0⟩ := hbij.2 (cc e)
  have hfix := fun x => ((hostReal_at hqd h).2 x).1
  let τ : hostE ζ a b ≃ₐ[hostF ζ a b] hostE ζ a b :=
    AlgEquiv.ofRingEquiv (f := σ0.toRingEquiv) (fun r => (hfix _).mp r.2 σ0 hσ0)
  rcases cases (hostE ζ a b) τ with h1 | h1
  · exfalso
    have hσ1 : σ0 = 1 := AlgEquiv.ext fun x => DFunLike.congr_fun h1 x
    have g1 : galE e ζ a b 1 = 1 := map_one (MonoidHom.mk' (galE e ζ a b) hmul)
    rw [hσ1, g1] at hσ0
    have := congrArg (fun x : GG e => ((x.1.1 : ℤˣ) : ℤ)) hσ0
    simp [cc, c0] at this
  · have hc : cQ hqd h = σ0 :=
      AlgEquiv.ext fun x => (DFunLike.congr_fun h1 x).symm
    rw [hc, hσ0]

end Host

end Eta

open Eta

theorem hostEta : HostEta := by
  intro e q d hH L _ _ ζ a b hL
  have hqd : HypOdd q d := hH.toHypOdd
  haveI hCM : IsCMField (hostE ζ a b) := isCMField_hostE hqd hL
  obtain ⟨-, -, hmul, hbij⟩ := hostGalois e q d hqd L ζ a b hL
  have hc := galE_cQ hqd hL
  have hunr : ∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 (hostE ζ a b), IsCMField.complexConj (hostE ζ a b) • x - x ∈ P :=
    fun P hP hP0 hx => hostUnramEF e q d hH L ζ a b hL P hP hP0 (cQ hqd hL) hc (fun x => hx x)
  have hstab : ∀ P : Ideal (𝓞 (hostE ζ a b)),
      cQ hqd hL ∈ MulAction.stabilizer _ P ↔ IsCMField.complexConj (hostE ζ a b) • P = P :=
    fun P => MulAction.mem_stabilizer_iff
  have hbot : ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (hostE ζ a b)))
      [P.LiesOver (span {(p : ℤ)})], P ≠ ⊥ := by
    intro p hp P _
    have hne : span {(p : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hne P
  refine ⟨fun 𝔭 h𝔭 h0 => ?_, ?_, ?_⟩
  · haveI := h𝔭
    exact Eta.split_or_inert (hostE ζ a b) hunr 𝔭 h0
  · intro p _ hp2 hpq hpd P _ _ σ hσ
    have hF := hostFrob_of hostGalois hostGalSpec e q d hqd L ζ a b hL p hp2 hpq hpd P
    have key := Eta.ncard_eq_two_iff (hostE ζ a b) hunr P (hbot p P)
    have hM : ∀ (τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (k : ℕ),
        galE e ζ a b (τ ^ k) = galE e ζ a b τ ^ k :=
      fun τ k => map_pow (MonoidHom.mk' (galE e ζ a b) hmul) τ k
    have hE : etaF ζ a b (P.comap (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)))) = -1 ↔
        cQ hqd hL ∈ MulAction.stabilizer _ P := by
      rw [hstab]
      unfold etaF
      split_ifs with h2
      · constructor
        · intro h; exact absurd h (by norm_num)
        · intro h; exact absurd h (key.mp h2)
      · constructor
        · intro _
          by_contra hne
          exact h2 (key.mpr hne)
        · intro _; rfl
    rw [hE]
    constructor
    · intro hs
      obtain ⟨k, ρ, hρ, hck⟩ := Decomp.stab_eq_inertia_mul p P σ (cQ hqd hL) hσ hs
      have hρ1 : ρ = 1 := (hF.2.2 ρ).mp hρ
      rw [hρ1, one_mul] at hck
      have hk : galE e ζ a b σ ^ k = cc e := by rw [← hM, ← hck, hc]
      generalize galE e ζ a b σ = g at hk ⊢
      obtain ⟨⟨s1, s2⟩, h⟩ := g
      have e1 : s1 ^ k = -1 := by simpa [cc, c0] using congrArg (fun x : GG e => x.1.1) hk
      have e2 : s2 ^ k = -1 := by simpa [cc, c0] using congrArg (fun x : GG e => x.1.2) hk
      have e3 : h ^ k = 1 := by simpa [cc, c0] using congrArg (fun x : GG e => x.2) hk
      have hs : ∀ s : ℤˣ, s ^ k = -1 → s = -1 := by
        intro s hsk
        rcases Int.units_eq_one_or s with rfl | rfl
        · exfalso
          have := congrArg (fun u : ℤˣ => (u : ℤ)) hsk
          simp at this
        · rfl
      have hs1 := hs s1 e1
      have hs2 := hs s2 e2
      have hodd : ¬ 2 ∣ k := by
        rintro ⟨m, rfl⟩
        rw [hs1, pow_mul] at e1
        have := congrArg (fun u : ℤˣ => (u : ℤ)) e1
        simp at this
      have hcardU : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
          Nat.totient_prime_pow Nat.prime_two (by omega)]
        simp
      have hdvd : orderOf h ∣ 2 ^ (e + 1) := by
        rw [← hcardU]
        exact (orderOf_dvd_natCard h).trans (Subgroup.index_dvd_card _)
      obtain ⟨j, -, hoj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hok : orderOf h ∣ k := orderOf_dvd_of_pow_eq_one e3
      have hj0 : j = 0 := by
        by_contra hj0
        apply hodd
        rw [hoj] at hok
        exact (dvd_pow_self 2 hj0).trans hok
      have hh1 : h = 1 := by
        rw [hj0, pow_zero] at hoj
        exact orderOf_eq_one_iff.mp hoj
      rw [hs1, hs2, hh1]
      rfl
    · intro hg
      have hσc : σ = cQ hqd hL := hbij.1 (hg.trans hc.symm)
      rw [← hσc]
      exact hσ.mem_stabilizer
  · intro p _ hp P _ _
    have key := Eta.ncard_eq_two_iff (hostE ζ a b) hunr P (hbot p P)
    have hnot := hostDecompConj e q d hH L ζ a b hL (cQ hqd hL) hc p hp P
    have h2 := key.mpr (fun h => hnot ((hstab P).mpr h))
    unfold etaF
    split_ifs with h3
    · rfl
    · exact absurd h2 h3

end Formalism.FrobeniusOrbits
