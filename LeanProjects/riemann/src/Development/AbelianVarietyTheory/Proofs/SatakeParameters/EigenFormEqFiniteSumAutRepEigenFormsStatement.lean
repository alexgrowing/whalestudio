import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenForms
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (C : Subgroup (UA E n)) (χ : C →* ℂˣ) (f : algForms W), (∀ (c : C) v g, f.1 v (g * c) = (χ c : ℂ) * f.1 v g) → ∃ (I : Finset (AutSub E n)) (F : AutSub E n → algForms W), (∀ π ∈ I, F π ∈ π.finPart W) ∧ (∀ π ∈ I, ∀ (c : C) v g, (F π).1 v (g * c) = (χ c : ℂ) * (F π).1 v g) ∧ f = ∑ π ∈ I, F π := by
  first | (exact @GlobalTheory.EigenDecomp.eigen_decomp) | (exact GlobalTheory.EigenDecomp.eigen_decomp) | (intros; apply GlobalTheory.EigenDecomp.eigen_decomp  <;> assumption)
