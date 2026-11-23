import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90LocallyConstantCocycle
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eq_div_of_locallyConstant_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : (Ω ≃ₐ[K] Ω) → Ωˣ),
  IsLocallyConstant w → (∀ g h, ((w (g * h) : Ωˣ) : Ω) = w g * g (w h)) → ∃ t : Ωˣ, ∀ g, ((w g : Ωˣ) : Ω) = g t / t := by
  first | exact @GlobalTheory.hilbert90_locallyConstant_cocycle | exact GlobalTheory.hilbert90_locallyConstant_cocycle | (intros; apply GlobalTheory.hilbert90_locallyConstant_cocycle <;> assumption)
