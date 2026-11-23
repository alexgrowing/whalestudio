import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_model_induces_root_metric : ∀ (D : D7) (O : Setup D), O.DualRef → ∀ (P : Finset ℕ) (c : O.s.Comp) (W : O.LatModel P c) (Q : Finset ℕ), Q ⊆ P → ∀ x : DV.Rt D.what₂.Tau O.N, W.V.Induces (O.root0 c Q x) (W.root Q x) 1 := by
  first | exact @GlobalTheory.Mean4O.Setup.induces_root0 | exact GlobalTheory.Mean4O.Setup.induces_root0 | (intros; apply GlobalTheory.Mean4O.Setup.induces_root0 <;> assumption)
