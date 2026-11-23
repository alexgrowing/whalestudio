import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal IntermediateField
open scoped Pointwise
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace CMIdealEquivalence

theorem map_KinE {L : Type} [Field L] [NumberField L] (ζ a b : L) :
    (KinE ζ a b).map (hostE ζ a b).val = Kd b := by
  have h := IntermediateField.adjoin_map (S := {bE ζ a b}) (f := (hostE ζ a b).val)
  rw [Set.image_singleton] at h
  exact h

def kEquiv {L : Type} [Field L] [NumberField L] (ζ a b : L) : KinE ζ a b ≃+* Kd b :=
  (((KinE ζ a b).equivMap (hostE ζ a b).val).trans
    (IntermediateField.equivOfEq (map_KinE ζ a b))).toRingEquiv

theorem mult_ring {M : Type} [Field M] [NumberField M]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) (hI : I ≠ 0) (x : M) :
    (∀ y ∈ I, x * y ∈ I) ↔ IsIntegral ℤ x := by
  constructor
  · intro h
    have hi : IsIntegral (𝓞 M) x :=
      isIntegral_of_smul_mem_submodule (I : Submodule (𝓞 M) M)
        (fun h0 => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h0))
        (FractionalIdeal.fg_of_isNoetherianRing le_rfl I) x (fun n hn => h n hn)
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro hx y hy
    have : (⟨x, hx⟩ : 𝓞 M) • y ∈ (I : Submodule (𝓞 M) M) :=
      Submodule.smul_mem (I : Submodule (𝓞 M) M) _ hy
    exact this

private theorem mem_one_iff'' {M : Type} [Field M] [NumberField M] (t : M) :
    t ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨x', rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe x'
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

private theorem integ_iff' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M) (t : M) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

private theorem smul_ne_bot' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M)
    (B : Ideal (𝓞 M)) (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  have h2 : σ⁻¹ • (σ • B) = σ⁻¹ • (⊥ : Ideal (𝓞 M)) := by rw [h]
  rwa [inv_smul_smul, Ideal.pointwise_smul_def, Ideal.map_bot] at h2

private theorem mem_inv_smul' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M)
    (B : Ideal (𝓞 M)) (hB : B ≠ ⊥) (y : M) :
    σ y ∈ ((σ • B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (nonZeroDivisors (𝓞 M)) M))⁻¹ := by
  have hc : ∀ b : 𝓞 M, algebraMap (𝓞 M) M (σ • b) = σ (algebraMap (𝓞 M) M b) := fun b => rfl
  have h1 : ((σ • B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (smul_ne_bot' σ B hB)
  have h2 : ((B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hB
  rw [FractionalIdeal.mem_inv_iff h1, FractionalIdeal.mem_inv_iff h2]
  constructor
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have := h (σ (algebraMap (𝓞 M) M b)) ((FractionalIdeal.mem_coeIdeal _).2
      ⟨σ • b, Ideal.smul_mem_pointwise_smul σ b B hb, hc b⟩)
    rw [mem_one_iff'', ← map_mul, integ_iff'] at this
    rw [mem_one_iff'']
    exact this
  · intro h z hz
    obtain ⟨c, hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have hb : σ⁻¹ • c ∈ B := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hc'
    have := h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)
    rw [mem_one_iff''] at this ⊢
    have e : algebraMap (𝓞 M) M c = σ (algebraMap (𝓞 M) M (σ⁻¹ • c)) := by
      rw [← hc, smul_inv_smul]
    rw [e, ← map_mul, integ_iff']
    exact this

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  show (D.host.conj * D.host.conj) x = x
  rw [show D.host.conj * D.host.conj = 1 by
    simp only [Formalism.HC.HostRaw.conj, ← map_mul, Formalism.HC.Frame.cc_mul_cc, map_one]]
  rfl

theorem b_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h, Ideal.pointwise_smul_def, Ideal.map_bot, bot_sup_eq] at h2
  exact bot_ne_top h2

theorem ordinary (D : D7) : ∀ p : ℕ, p.Prime →
    (primesOver (span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2 →
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(p : ℤ)}) →
        ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, τ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P →
          (D.host.galE (σ * τ) ∈ D.R.Psi ↔
            D.host.galE σ ∈ D.R.Psi) := by
  intro p hp hK P hP hl σ τ hτ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hl
  exact (D.host.der.ordinary p P).2 hK σ τ hτ

end CMIdealEquivalence

open CMIdealEquivalence

def PolPart (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ →
    ∃ ξ : D.host.E, ξ ∈ D.host.K ∧ D.host.conj ξ = -ξ ∧ (∀ φ ∈ PhiEmb D, 0 < (φ ξ).im) ∧
      ∀ y : D.host.E,
        y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 ↔
        ∀ x ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0,
          Algebra.trace ℚ D.host.E (ξ * D.host.conj x * y) ∈ (algebraMap ℤ ℚ).range

theorem lemma_one_eight_of_polarisation (D : D7) (hPol : PolPart D) : Conclusion8 D := by
  have hb := b_ne_bot D
  have hσb : D.host.conj • D.host.𝔟 ≠ ⊥ := smul_ne_bot' D.host.conj _ hb
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hb
  refine ⟨D.host.AA0, ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹, ?_, ?_, ?_, ordinary D⟩
  · intro x
    have hσσ : D.host.conj • D.host.conj • D.host.𝔟 = D.host.𝔟 := by
      rw [smul_smul, show D.host.conj * D.host.conj = 1 from AlgEquiv.ext (conj_conj D), one_smul]
    have h := mem_inv_smul' D.host.conj (D.host.conj • D.host.𝔟) hσb x
    rw [hσσ] at h
    exact h.symm
  · rw [D.host.𝔟_spec.1, FractionalIdeal.coeIdeal_mul, mul_inv]
    try rfl
  · intro cc hcc
    have hm : Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hcc
    have hne : ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 ≠ 0 :=
      mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hm) (inv_ne_zero hb0)
    exact ⟨fun x => mult_ring _ hne x, hPol cc hcc⟩

end Formalism.MainNotions.UnusedSlot33

end
