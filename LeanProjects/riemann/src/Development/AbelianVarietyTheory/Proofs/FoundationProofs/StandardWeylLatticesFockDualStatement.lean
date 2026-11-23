import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_weyl_lattices_fock_dual : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (x : Pol K ι n), x ∈ VV K lam → ((∀ y ∈ delStd K lam, pairP lam (fun _ => 1) y x ∈ (algebraMap (𝓞 K) K).range) ↔ x ∈ nabStd K lam) ∧ ((∀ y ∈ nabStd K lam, pairP lam (fun _ => 1) y x ∈ (algebraMap (𝓞 K) K).range) ↔ x ∈ delStd K lam) := by
  first | exact @GlobalTheory.StdDual.std_dual | exact GlobalTheory.StdDual.std_dual | (intros; apply GlobalTheory.StdDual.std_dual <;> assumption)
