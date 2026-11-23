import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.TameInertiaTowers.TowerFieldFoundations
import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.JumpSets

open NumberField IntermediateField

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace ConjReal

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

lemma hcl_neg_one (e : ℕ) : hcl e (-1) = 1 := by
  unfold hcl
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers _

theorem conj_main (hGal : HostGalois) (hSpec : HostGalSpec) (hqd : HypOdd q d)
    (h : IsLayer (e + 2) q d ζ a b) :
    ∃ (τ : L ≃ₐ[ℚ] L) (σc : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b),
      galMap h.1 a b τ = JJ (e + 2) ∧ (∀ x : hostE ζ a b, ((σc x : hostE ζ a b) : L) = τ x) ∧
      galE e ζ a b σc = cc e ∧
      ∀ (φ : hostE ζ a b →+* ℂ) (x : hostE ζ a b), φ (σc x) = starRingEnd ℂ (φ x) := by
  obtain ⟨hG, _, _, _⟩ := hGal e q d hqd L ζ a b h
  have := hG
  obtain ⟨τ, hτ⟩ := (layerGalois (e + 2) q d (by omega) hqd L ζ a b h).2.2.2.2 (JJ (e + 2))
  let σc : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b := τ.restrictNormal (hostE ζ a b)
  have hres : ∀ x : hostE ζ a b, ((σc x : hostE ζ a b) : L) = τ x := fun x =>
    AlgEquiv.restrictNormal_commutes τ (hostE ζ a b) x
  refine ⟨τ, σc, hτ, hres, ?_, ?_⟩
  · rw [(hSpec e q d hqd L ζ a b h σc).2.2.2 τ hres, hτ]
    simp [JJ, cc, c0, hcl_neg_one]
  · intro φ x
    let ψ : L →+* ℂ := ComplexEmbedding.lift L φ
    have hψ : ∀ y : hostE ζ a b, ψ (y : L) = φ y := fun y =>
      ComplexEmbedding.lift_algebraMap_apply L φ y
    have hc := (layerConj (e + 2) q d (by omega) hqd L ζ a b h ψ τ).2 hτ
    rw [← hψ (σc x), ← hψ x, hres x]
    exact hc x

lemma aE_sq (h : IsLayer (e + 2) q d ζ a b) : aE ζ a b ^ 2 = -(q : hostE ζ a b) := by
  apply Subtype.ext
  push_cast
  exact h.2.1

end ConjReal

open ConjReal

theorem hostConj_of (hGal : HostGalois) (hSpec : HostGalSpec) : HostConj := by
  intro e q d hqd L _ _ ζ a b h
  obtain ⟨hG, _, _, hbij⟩ := hGal e q d hqd L ζ a b h
  have := hG
  obtain ⟨_, σc, _, _, hσc, hconj⟩ := conj_main hGal hSpec hqd h
  have hq : 0 < q := hqd.1.pos
  have haE := aE_sq h
  have hTC : IsTotallyComplex (hostE ζ a b) := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw (aE ζ a b)
    rw [ComplexEmbedding.conjugate_coe_eq, UnitConjugation.phi_conj hq haE] at h2
    have h3 : (2 : ℂ) * w.embedding (aE ζ a b) = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (UnitConjugation.ne_zero_of_sq hq haE) h4
  have hCM : IsCMField (hostE ζ a b) := by
    refine IsCMField.of_forall_isConj (hostE ζ a b) (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact (hconj φ x).symm
  refine ⟨hCM, fun φ σ => ⟨fun hx => ?_, fun hσ => ?_⟩⟩
  · have hσ : σ = σc := AlgEquiv.ext fun x => φ.injective (by rw [hx, hconj])
    rw [hσ, hσc]
  · have hσ' : σ = σc := hbij.1 (hσ.trans hσc.symm)
    subst hσ'
    exact hconj φ

theorem hostReal_of (hGal : HostGalois) (hSpec : HostGalSpec) (hConj : HostConj) : HostReal :=
  _root_.UpperTheory.Reformulated.B.JumpSetsAlt.hostReal_of hGal hSpec hConj

end Formalism.FrobeniusOrbits
