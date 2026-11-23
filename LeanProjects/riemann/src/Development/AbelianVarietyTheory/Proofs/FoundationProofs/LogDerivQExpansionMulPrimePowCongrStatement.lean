import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongr
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDerivQExpansion_mul_primePow_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime], (l : Ω) ∈ A.nonunits → ∀ (n : ℕ) (f u : X.K), f ≠ 0 → u ≠ 0 → X.sl (ofSL ModularGroup.T) u = u → ∀ φ φ' : HahnSeries ℚ Ω, IsDl X A l n 1 f φ → IsDl X A l n 1 (f * u ^ (l ^ n)) φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  exact @GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong Ω _ _ _
