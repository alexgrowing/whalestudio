import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePadicSpanOfPowPMulMem
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω), (∀ t, IsInt p (E t) ∧ IsAlgZp p (E t)) → ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω), (∀ j, IsInt p (f j) ∧ IsAlgZp p (f j)) ∧ ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt p y → (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t → ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  first | exact @GlobalTheory.GeoFix.exists_fin_span_of_pow_mul | exact GlobalTheory.GeoFix.exists_fin_span_of_pow_mul | (intros; apply GlobalTheory.GeoFix.exists_fin_span_of_pow_mul <;> assumption)
