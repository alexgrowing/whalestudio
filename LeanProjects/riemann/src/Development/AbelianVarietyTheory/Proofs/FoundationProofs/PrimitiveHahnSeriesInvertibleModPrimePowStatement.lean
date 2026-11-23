import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesInvertibleModPrimePow
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P : HahnSeries ℚ Ω), 0 < L → Prim A P → (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → ∃ Q : HahnSeries ℚ Ω, (∀ r, Q.coeff r ∈ A) ∧ (∀ r : ℚ, Q.coeff r ≠ 0 → (r * L).den = 1) ∧ ∀ r, CgA A l n ((Q * P).coeff r) ((1 : HahnSeries ℚ Ω).coeff r) := by
  first | exact @GlobalTheory.prim_inv_mod_pow | exact GlobalTheory.prim_inv_mod_pow | (intros; apply GlobalTheory.prim_inv_mod_pow <;> assumption)
