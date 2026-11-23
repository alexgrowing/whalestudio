import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalConjOfNotGood
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_local_conj_of_not_good : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), ¬ Formalism.L2.PjFree.GoodEmb κ.c σ → HodgeLocal x ((starRingEnd ℂ).comp σ) → HodgeLocal x σ := by
  first | exact @GlobalTheory.CurvInterp.HodgeConj.hodgeLocal_of_conj | exact GlobalTheory.CurvInterp.HodgeConj.hodgeLocal_of_conj | (intros; apply GlobalTheory.CurvInterp.HodgeConj.hodgeLocal_of_conj <;> assumption)
