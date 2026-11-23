import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.EmbOnto

theorem embAt_surj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C] [Algebra c.F C] (φ : E →+* C) :
    ∃ σ : E →+* ℂ, embAt c C σ = φ := by
  have hinj : Function.Injective (fun σ : E →+* ℂ => embAt c C σ) := by
    intro σ τ h
    ext a
    have h1 : embF c σ a = embF c τ a := (algebraMap c.F C).injective (DFunLike.congr_fun h a)
    have h2 := congrArg (fun x : c.F => (x : ℂ)) h1
    exact h2
  have hb := Function.Injective.bijective_of_nat_card_le hinj (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, NumberField.Embeddings.card,
      NumberField.Embeddings.card])
  exact hb.2 φ

end GlobalTheory.EmbOnto
