import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationModIntegralAlmostDualPSqIsInt
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationModIntegral_almostDual_p_sq_isInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt p (D (tr (u l * (x * v k))))) → IsInt p ((p : Ω) ^ 2 * D x) := by
  first | exact @GlobalTheory.KumDlog.der_dual_p_sq_int | exact GlobalTheory.KumDlog.der_dual_p_sq_int | (intros; apply GlobalTheory.KumDlog.der_dual_p_sq_int <;> assumption)
