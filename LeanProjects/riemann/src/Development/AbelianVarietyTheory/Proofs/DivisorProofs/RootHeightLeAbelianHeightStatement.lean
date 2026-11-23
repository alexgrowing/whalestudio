import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootHeightLeAbelianHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_height_le_abelian_height : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → (∀ (P : Finset ℕ) (c : O.s.Comp), O.LatModel P c) → ∀ (c : O.s.Comp) (x : DV.Rt D.what₂.Tau O.N), ∃ C : ℝ, ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) → |(O.root0 c ∅ x).ht b| ≤ C * (|(O.met.ab c).ht b| + 1) := by
  first | exact @GlobalTheory.RootHtBound.root_ht_le | exact GlobalTheory.RootHtBound.root_ht_le | (intros; apply GlobalTheory.RootHtBound.root_ht_le <;> assumption)
