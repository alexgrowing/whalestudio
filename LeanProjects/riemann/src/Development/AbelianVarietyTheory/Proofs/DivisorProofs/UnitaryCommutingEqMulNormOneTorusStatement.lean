import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCommutingEqMulNormOneTorus
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_commuting_eq_mul_normOneTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h : GLw n w, h ∈ UL n w → h * γ = γ * h → torusOf w B ψ h ∈ B.T ∧ ∀ y, ψ ((torusOf w B ψ h : B.A) * y) = h.val *ᵥ ψ y := by
  first | exact @GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute | exact GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute | (intros; apply GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute <;> assumption)
