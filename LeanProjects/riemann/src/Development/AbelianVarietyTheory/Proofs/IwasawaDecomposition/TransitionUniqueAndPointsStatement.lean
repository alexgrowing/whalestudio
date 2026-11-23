import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransitionUniqueAndPoints
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transition_unique_and_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i i₂ : Idx H p) (τ τ' : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ) (mu' : SABMap (Y i₂).t (Y i).t τ'), i.c.F ≤ i₂.c.F → IsTrans i i₂ τ mu → IsTrans i i₂ τ' mu' → τ = τ' ∧ ∀ (k : Type) [Field k] (y : Sp k ⟶ (Xo i₂.l).XF i₂.c) (T : Scheme.{0}) (s : T ⟶ Sp k) (g : T ⟶ (Y i₂).t.G.left), g ≫ (Y i₂).t.G.hom = s ≫ y ≫ (Y i₂).j → g ≫ mu.φ = g ≫ mu'.φ := by
  first | exact @GlobalTheory.TransUniq.trans_unique | exact GlobalTheory.TransUniq.trans_unique | (intros; apply GlobalTheory.TransUniq.trans_unique <;> assumption)
