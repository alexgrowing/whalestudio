import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_flat_abelianSchemeHom_of_quasiInverse : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (c : ℕ), c ≠ 0 → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ c → ψ' ≫ ψ = (𝟙 A') ^ c → IsFinite ψ.left ∧ Flat ψ.left := by
  first | (exact @GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse) | (exact GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse) | (intros; apply GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse <;> assumption)
