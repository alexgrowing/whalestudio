import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemCommonRefinement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_common_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (n : ℕ) (Z : Fin (n + 1) → Mdl Y i₀), (∀ a, (Z a).i = (Z 0).i ∧ (Z a).ty = (Z 0).ty) → ∃ Z' : Mdl Y i₀, Z'.i = (Z 0).i ∧ Z'.ty = (Z 0).ty ∧ ∀ a, ∃ f : Z'.X ⟶ (Z a).X, IsMap Z' (Z a) f := by
  first | exact @GlobalTheory.ShFam.Pad.exists_dominating_model | exact GlobalTheory.ShFam.Pad.exists_dominating_model | (intros; apply GlobalTheory.ShFam.Pad.exists_dominating_model <;> assumption)
