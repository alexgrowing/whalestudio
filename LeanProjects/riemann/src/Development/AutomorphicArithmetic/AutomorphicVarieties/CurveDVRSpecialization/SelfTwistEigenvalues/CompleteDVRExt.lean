import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
open Polynomial Matrix

theorem UpperTheory.V.Pr.T.completeDVRExt :
    ∀ {A K L : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
      [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L],
      Module.Finite A (integralClosure A L) ∧ IsDiscreteValuationRing (integralClosure A L) := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _ _
  exact ⟨GlobalTheory.FormalIsogeny.finite_integralClosure A K L,
    GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure A K L⟩
