import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPolarizedAbelian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_product_polarized_abelian : ∀ (S : Scheme.{0}) (P₁ P₂ : PPAS S), ∃ P : PPAS S, P.IsProd P₁ P₂ := by
  first | exact @GlobalTheory.PPAS.exists_isProd | exact GlobalTheory.PPAS.exists_isProd | (intros; apply GlobalTheory.PPAS.exists_isProd <;> assumption)
