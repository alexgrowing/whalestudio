import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplEx

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.regular :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (B : Type) [CommRing B] [IsLocalRing B]
      [Algebra R B], IsCplAt R p B → IsRegularLocalRing (Localization.AtPrime p) →
      IsRegularLocalRing B ∧ ringKrullDim B = ringKrullDim (Localization.AtPrime p) := by
  intro R _ _ p _ B _ _ _ hB hT
  obtain ⟨e⟩ := IsCplAt.nonempty_algEquiv R p B (CplAt R p) hB (isCplAt_cplAt R p)
  have hC : IsRegularLocalRing (CplAt R p) :=
    GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion (Localization.AtPrime p)
  refine ⟨IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm, ?_⟩
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ← hC.spanFinrank_maximalIdeal,
    ← hT.spanFinrank_maximalIdeal]
  exact congrArg _ (AdicCompletion.spanFinrank_maximalIdeal_eq (R := Localization.AtPrime p))
