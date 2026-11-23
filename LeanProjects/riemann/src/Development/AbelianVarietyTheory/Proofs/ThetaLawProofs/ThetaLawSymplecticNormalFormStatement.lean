import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawSymplecticNormalForm
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.theta_law_symplectic_normal_form : ∀ (x : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ) (sp : Matrix (Fin x.P.g ⊕ Fin x.P.g) (Fin x.P.g ⊕ Fin x.P.g) ℤ) (n n' k k' : Fin x.P.g → ℤ), sp ∈ Matrix.symplecticGroup (Fin x.P.g) ℤ → GlobalTheory.KeyPow.ThetaLaw x.P.g sp n n' k k' → c ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) c → ∃ (M' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c' : ℂ), c' ≠ 0 ∧ M'.det ^ 4 / c' ^ 8 = M.det ^ 4 / c ^ 8 ∧ GlobalTheory.KeyPow.NormalAt x (Key.Chi.spAct sp τ) M' (fun i => (k i : ℂ) / 2) (fun i => (k' i : ℂ) / 2) c' := by
  first | exact @GlobalTheory.SpMove.normalAt_spAct | exact GlobalTheory.SpMove.normalAt_spAct | (intros; apply GlobalTheory.SpMove.normalAt_spAct <;> assumption)
