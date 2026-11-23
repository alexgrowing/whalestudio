import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZmodCocycleEqCoboundaryOfUnitTwistedCocycle
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90LocallyConstantCocycleStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyConstant_zmod_coboundary_of_mu_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  first | exact @GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle | exact GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle | (intros; apply GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle <;> assumption)
