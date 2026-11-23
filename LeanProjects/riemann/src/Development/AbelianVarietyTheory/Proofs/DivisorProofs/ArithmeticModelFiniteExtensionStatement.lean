import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_model_finite_extension : ∀ (F : Type) [Field F] [NumberField F] (G T : Scheme.{0}) (s : G ⟶ Sp F) (S : Set G) (d : ℕ) (ι : G ⟶ T) (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp (𝓞 F)) (jB : W ⟶ X) (πB : W ⟶ G) (ρ : X ⟶ T), IsPre s S d ι q jB πB ρ → ∀ (K : Type) [Field K] [Algebra X.functionField K], Module.Finite X.functionField K → ∃ (X' W' : Scheme.{0}) (_ : IsIntegral X') (ν : X' ⟶ X) (jB' : W' ⟶ X') (πB' : W' ⟶ G) (κ : K →+* X'.functionField), IsPre s S d ι (ν ≫ q) jB' πB' (ν ≫ ρ) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ X'.fromSpecStalk (genericPoint X') ≫ ν = spMap κ ≫ spMap (algebraMap X.functionField K) ≫ X.fromSpecStalk (genericPoint X) := by
  first | exact @GlobalTheory.ArLieBase.normalization_isPre | exact GlobalTheory.ArLieBase.normalization_isPre | (intros; apply GlobalTheory.ArLieBase.normalization_isPre <;> assumption)
