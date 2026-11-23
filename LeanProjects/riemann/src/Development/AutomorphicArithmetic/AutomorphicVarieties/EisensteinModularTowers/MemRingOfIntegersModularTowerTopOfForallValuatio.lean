import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet
import Mathlib.RingTheory.Valuation.LocalSubring

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 Polynomial
attribute [local instance] algMdl algPoly algRat

private theorem valCrit {R K : Type} [CommRing R] [Field K] (A : R →+* K) (x : K)
    (h : ∀ V : ValuationSubring K, (∀ r, A r ∈ V) → x ∈ V) : A.IsIntegralElem x := by
  letI := A.toAlgebra
  by_contra hx
  have hx' : x ∉ (integralClosure R K).toSubring := hx
  obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx'
  exact hxV (h V fun r => hV ((integralClosure R K).algebraMap_mem r))

theorem UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (f : topL X M), (∀ W : ValuationSubring X.K, X.OverY W → (f : X.K) ∈ W) → f ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  intro Ω _ _ ε X M f hf
  have key := valCrit ((topL X M).subtype.comp (algebraMap (Polynomial Ω) (topL X M))) (f : X.K) (by
    intro V hV
    apply hf V
    refine ⟨fun c => ?_, ?_⟩
    · have h1 := hV (Polynomial.C c)
      change ((jPoly X _ (Polynomial.C c) : X.K)) ∈ V at h1
      rwa [coe_jPoly, Polynomial.aeval_C] at h1
    · have h2 := hV Polynomial.X
      change ((jPoly X _ Polynomial.X : X.K)) ∈ V at h2
      rwa [coe_jPoly, Polynomial.aeval_X] at h2)
  exact RingHom.IsIntegralElem.of_map Subtype.val_injective key
