import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgCStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgClosedResidueFieldOfAic
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.Gal.Mod.spValsub :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (V : ValuationSubring Ω), AIC V ∧ SH V := by
  intro Ω _ _ V
  have hclosed : IsAlgClosed (FractionRing V) :=
    IsAlgClosed.of_ringEquiv Ω (FractionRing V)
      (IsLocalization.algEquiv (nonZeroDivisors V) Ω (FractionRing V)).toRingEquiv
  have hA : AIC V := (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed V).2 ⟨inferInstance, hclosed⟩
  exact ⟨hA, GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hA⟩
