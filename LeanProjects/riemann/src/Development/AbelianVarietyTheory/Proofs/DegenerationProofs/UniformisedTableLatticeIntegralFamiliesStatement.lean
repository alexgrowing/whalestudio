import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTableLatticeIntegralFamilies
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_table_lattice_integral_families : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ m n : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → n.Prime → Odd n → IsUnit (n : V) → ∀ O : ValuationSubring F, (∀ x, x ∈ O ↔ 0 ≤ v x) → ∀ (r : ℕ) (cls : Fin r → D.toPre.X) (b τ : Fin r → SecA A F (m ^ 2)) (s : Fin r → Fam D.toPre F (m ^ 2)) (B : Matrix (Fin r) (Fin r) F), Norms D Q v (m ^ 2) cls s → (∀ i, U.ExpandsF F (m ^ 2) w₀ (b i) (s i)) → (∀ t, ∃! a, Cmb τ a t) → (∀ i, Cmb τ (B i) (b i)) → ∀ (d : ℕ) (κ : F), v κ = (((d : ℚ) * (∑ i, (Q (cls i) : ℚ)) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) → (tab ρ m th τ).Loc O B n d κ := by
  first | exact @GlobalTheory.OneBasis.UnifLoc.main | exact GlobalTheory.OneBasis.UnifLoc.main | (intros; apply GlobalTheory.OneBasis.UnifLoc.main <;> assumption)
