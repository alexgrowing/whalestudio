import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerChainMatricesWithNormBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerChain_matrices_with_norm_bounds : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms) (g : Q.S₁.EqFun →ₗ[K] Module.Dual K (Fin (Df.nV Bs.μ0) → K)) (Pl : Type) [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) (hn : HtNums R (InfinitePlace K)) (no : Bs.J → ℕ) (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ), (∀ v, IsUnit (Dc.Xc u v).det) → (∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) v x ^ 2 : ℝ) : ℂ) = famIpAt (Q.F 0) (Q.hF 0) v (f0 x) (f0 x)) → (∀ i, FamFramed (Q.F i) (Q.hF i)) → DatFramed Q.S₁ Q.hS₁ → (∀ φ F, Dc.Pt u Bs.μ0 φ F = g (Q.col (f0 φ)) F) → IsFrames Df X0 → FactorBounds Q no hn.sz → (∀ (v : InfinitePlace K) (ψ : Q.S₁.EqFun) F, v (g ψ F) ^ 2 ≤ Real.exp hn.hPn * (Q.S₁.ipAt Q.hS₁ v ψ ψ).re * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody Dc u Q f0 R := by
  first | exact @GlobalTheory.DefRowsChain.rowsBody_of_framed | exact GlobalTheory.DefRowsChain.rowsBody_of_framed | (intros; apply GlobalTheory.DefRowsChain.rowsBody_of_framed <;> assumption)
