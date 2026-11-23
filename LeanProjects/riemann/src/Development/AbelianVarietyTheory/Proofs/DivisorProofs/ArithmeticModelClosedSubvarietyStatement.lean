import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelClosedSubvariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_model_closed_subvariety : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] (e : F ≃+* F') (T : Scheme.{0}) (sT : T ⟶ Sp (𝓞 F')), IsProjOver sT → ∀ (V : Scheme.{0}) [IsIntegral V] (j : V ⟶ Limits.pullback sT (spMap (algebraMap (𝓞 F') F'))), IsClosedImmersion j → ∀ d : ℕ, topologicalKrullDim V = d → ∃ (X W : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ Limits.pullback sT (spMap (algebraMap (𝓞 F') F'))) (ρ : X ⟶ T), IsPre (Limits.pullback.snd sT (spMap (algebraMap (𝓞 F') F')) ≫ spMap e.toRingHom) (Set.range j) d (Limits.pullback.fst sT (spMap (algebraMap (𝓞 F') F'))) q jB πB ρ := by
  first | exact @GlobalTheory.ArLieBase.exists_isPre_closure | exact GlobalTheory.ArLieBase.exists_isPre_closure | (intros; apply GlobalTheory.ArLieBase.exists_isPre_closure <;> assumption)
