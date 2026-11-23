import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSumHeisenbergIsEigenvector
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_heisenberg_isEigenvector : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (Λd : AddSubgroup (WO S T)) (R : Finset (WO S T)) (x : WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ ∀ u ∈ Λd, ψ (symplO S T u y) = 1) → (∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → ∃ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) → (∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) → y = y') → (∀ a ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf (cA D e) a → ψ (symplO S T x a) = 1) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → ∀ y, IsHalf (cA D e) y → (∀ u ∈ Λd, ψ (symplO S T u y) = 1) → heisO ψ S T y (∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g) = ψ (symplO S T x y) • ∑ z ∈ R, ψ (-symplO S T x z) • heisO ψ S T z g := by
  first | exact @GlobalTheory.CosetEigen.cosetSum_eigen | exact GlobalTheory.CosetEigen.cosetSum_eigen | (intros; apply GlobalTheory.CosetEigen.cosetSum_eigen <;> assumption)
