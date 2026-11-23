import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormGLZetaSumTrivialParameterSubOneLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_GL_zetaSum_trivialParameter_sub_one_le : ∀ (q : ℕ), 2 ≤ q → ∀ (r t : ℕ), r + 5 ≤ t → ∀ (B : Multiset ℂˣ), B.card = r → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ X : ℂ, ‖X‖ = (q : ℝ) ^ (-((1 + (t : ℝ)) / 2)) → ‖eulerFac B X * eulerFac (B.map fun β => β⁻¹) X * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℂ) ^ i)⁻¹) - 1‖ ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  first | exact @GlobalTheory.GLZetaBound.norm_trivial_sub_one_le | exact GlobalTheory.GLZetaBound.norm_trivial_sub_one_le | (intros; apply GlobalTheory.GLZetaBound.norm_trivial_sub_one_le <;> assumption)
