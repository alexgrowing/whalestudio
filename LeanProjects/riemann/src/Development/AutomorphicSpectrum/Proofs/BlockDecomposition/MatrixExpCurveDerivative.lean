import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.ExpCurve

section Entries

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  haveI : FiniteDimensional ℝ (Mat n) := inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
  haveI : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)
  have h : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n))
      (NormedSpace.exp (t • X) * X : Mat n) t := hasDerivAt_exp_smul_const X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

end Entries

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  exact hasDerivAt_exp_entry X t i j

theorem expC_continuous_hasDerivAt :
    ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  intro n X
  refine ⟨?_, hasDerivAt_exp X⟩
  refine (GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG (n := n)).isInducing.continuous_iff.2 ?_
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp X t).continuousAt

end GlobalTheory.CompanionTheory.PresSobA.ExpCurve
