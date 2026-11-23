import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalZetaSumsAbsolutelyConvergentUniform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localZetaSums_absolutely_convergent_uniform : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ), (∀ w, ‖(z w : ℂ)‖ = 1) → ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (φ : ∀ v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}, Gv V v.1 → ℂ), (∀ v, IsLocKer V D.R.nV z v.1 (φ v)) → ∃ A : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} → ℝ, Summable (fun v => A v - 1) ∧ ∀ v, HasSum (fun a : Gv V v.1 ⧸ Kv V v.1 => ‖φ v a.out‖) (A v) := by
  first | exact @GlobalTheory.FinZeta.AbsConv.absConv_localZeta | exact GlobalTheory.FinZeta.AbsConv.absConv_localZeta | (intros; apply GlobalTheory.FinZeta.AbsConv.absConv_localZeta <;> assumption)
