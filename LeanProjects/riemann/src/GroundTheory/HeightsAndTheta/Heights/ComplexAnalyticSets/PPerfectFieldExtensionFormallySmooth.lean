import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPerfectFieldExtensionFormallySmooth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPerfectFieldExtensionFormallySmoothExtensionStep
set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem formallySmooth_of_perfectField_of_charP [PerfectField F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] :
    Algebra.FormallySmooth F K := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ N hN u => ?_
  have hpB : (p : B) = 0 := by rw [← map_natCast (algebraMap F B), CharP.cast_eq_zero, map_zero]
  set P := sqZeroFrobeniusLift N hp.out hpB hN
  set ψ : K →+* B := P.comp u.toRingHom
  have hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p := fun z c hc => by
    show P (u z) = c ^ p
    rw [← hc, sqZeroFrobeniusLift_mk]
  obtain ⟨σ₀, hσ₀⟩ := exists_isGoodPartialLift_frobenius (K := K) p hpB hN u
  have : Nonempty {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ} :=
    ⟨⟨σ₀, hσ₀⟩⟩
  obtain ⟨⟨⟨L, φ⟩, hgood⟩, hm⟩ := exists_maximal_of_nonempty_chains_bounded
    (r := fun a b : {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ} =>
      PartialLiftLE a.1 b.1)
    (exists_isGoodPartialLift_upperBound (p := p) (N := N) (u := u) (ψ := ψ)) (fun hab hbd => hab.trans hbd)
  have htop : (⊤ : IntermediateField F K) ≤ L := by
    intro x _
    by_contra hx
    obtain ⟨σ, hσ, hle, hxσ⟩ := exists_isGoodPartialLift_extend p hψ hgood hx
    exact hx ((hm ⟨σ, hσ⟩ hle).1 hxσ)
  refine ⟨φ.comp ((IntermediateField.inclusion htop).comp IntermediateField.topEquiv.symm.toAlgHom), ?_⟩
  ext x
  exact hgood.2 _

theorem formallySmooth_of_charZero [CharZero F] : Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  have := hs.isAlgebraic_field
  have : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  exact .of_algebraicIndependent_of_isSeparable hs.1

end

theorem PerfectFieldExtensionFormallySmooth.proof : PerfectFieldExtensionFormallySmooth.Statement := by
  intro F K _ _ _ _
  obtain ⟨p, hchar⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hp | rfl
  · have := Fact.mk hp
    exact formallySmooth_of_perfectField_of_charP p
  · have := CharP.charP_to_charZero F
    exact formallySmooth_of_charZero

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
