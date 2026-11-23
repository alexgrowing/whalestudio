import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartResidueTrdegEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_residue_trdeg_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
    (Z : Mdl Y i₀), (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → ∀ (a : Fin Z.m) (x : Sp Γ(Z.X, (Z.U a).1)),
    @Algebra.trdeg ((Y Z.i).X.residueField ((Z.chart a ≫ Z.π) x)) ((Sp Γ(Z.X, (Z.U a).1)).residueField x) _ _
      ((Z.chart a ≫ Z.π).residueFieldMap x).hom.toAlgebra ≤ ((∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 : ℕ) : Cardinal) := by
  first | exact @GlobalTheory.LocM.FibTrdeg.trdeg_residueField_le | exact GlobalTheory.LocM.FibTrdeg.trdeg_residueField_le | (intros; apply GlobalTheory.LocM.FibTrdeg.trdeg_residueField_le <;> assumption)
