import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumns
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_symplectic_unitary_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∃ s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ, ∀ x ∈ X.dom, tauMat X bas idx x ∈ Siegel (Fin g) ∧ spAct s (blk n (tauMat X bas idx x)) = blk n (tauMat X bas idx x) ∧ (spDen s (blk n (tauMat X bas idx x))).det * ∏ i : Fin g, rowType X (idx i) h.det = 1 ∧ ∀ z : Fin n → Fin g → ℂ, (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) ᵥ* (spDen s (blk n (tauMat X bas idx x)))⁻¹ = fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  first | exact @GlobalTheory.ColumnSymplectic.exists_symplectic_columns | exact GlobalTheory.ColumnSymplectic.exists_symplectic_columns | (intros; apply GlobalTheory.ColumnSymplectic.exists_symplectic_columns <;> assumption)
