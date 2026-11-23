import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemLevelGrowth
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_level_growth : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (i : Idx H p) (n : ℕ), i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → p ^ n ∣ i.l.A → 1 + 1 / ((p : ℝ) - 1) < n → ∀ st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z true st x) := by
  first | exact @GlobalTheory.HTLine.exists_lineModel_hodgeTate | exact GlobalTheory.HTLine.exists_lineModel_hodgeTate | (intros; apply GlobalTheory.HTLine.exists_lineModel_hodgeTate <;> assumption)
