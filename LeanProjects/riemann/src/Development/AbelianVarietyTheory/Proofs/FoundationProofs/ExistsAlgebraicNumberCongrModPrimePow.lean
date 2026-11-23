import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicElementApproximation
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.DenseAlg

theorem exists_mem_cong : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
    (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ (k : ℕ) (e : Ωl), IsInt p e → IsAlgZp p e → ∃ a ∈ A, Cong p k e (j a) := by
  intro Ω _ _ _ p _ A Ωl _ _ hclo j hA k e he halg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨a, ha, hc⟩ := GlobalTheory.K5.Dense.exists_cong p Ωl hclo Ω j k e he halg
  exact ⟨a, (hA a).2 ha, hc⟩

end GlobalTheory.K5.DenseAlg
