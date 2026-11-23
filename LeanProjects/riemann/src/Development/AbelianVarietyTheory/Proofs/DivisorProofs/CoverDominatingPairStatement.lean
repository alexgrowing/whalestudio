import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverDominatingPair
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_dominating_pair : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (W V : Mean4O.Cover Y) (k : W.G ⟶ V.G),
    k ≫ V.π = W.π →
    ∃ (W' : Mean4O.Cover Y) (a : W'.X ⟶ W.X) (b : W'.X ⟶ V.X), a ≫ W.p = W'.p ∧ b ≫ V.p = W'.p ∧
      Lies W' W a ∧ Lies W' V b := by
  first | exact @GlobalTheory.Mean4O.CoverDom.exists_cover_dominating_cover | exact GlobalTheory.Mean4O.CoverDom.exists_cover_dominating_cover | (intros; apply GlobalTheory.Mean4O.CoverDom.exists_cover_dominating_cover <;> assumption)
