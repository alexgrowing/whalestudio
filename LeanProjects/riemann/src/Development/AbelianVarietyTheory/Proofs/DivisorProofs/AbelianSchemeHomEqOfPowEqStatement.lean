import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfPowEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hom_eq_of_pow_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (d : ℕ), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → ∀ (x y : B ⟶ A), IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y := by
  first | (exact @GlobalTheory.HomTorsionFree.eq_of_pow_eq) | (exact GlobalTheory.HomTorsionFree.eq_of_pow_eq) | (intros; apply GlobalTheory.HomTorsionFree.eq_of_pow_eq  <;> assumption)
