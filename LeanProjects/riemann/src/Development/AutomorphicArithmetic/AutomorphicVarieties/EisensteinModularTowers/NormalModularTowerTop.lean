import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.NormalModularTowerTopAlgebraModel
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 Polynomial
attribute [local instance] algMdl algPoly algRat

attribute [-instance] UpperTheory.V.Alg.IsCO.toIsLocalRing in
theorem UpperTheory.normal_modularTowerTop :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {M : ℕ}, M ≠ 0 → Normal (topF X M) (topL X M) := by
  intro Ω _ _ _ ε X M hM
  exact UpperTheory.normal_modularTowerTop_algebraModel X M hM
