import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

variable {D : D7} {V : HSp D} {r : ℕ}

def firstCols (X : Matrix (Fin V.rank) (Fin r) D.host.E) (j : Fin r) :
    Matrix (Fin V.rank) (Fin (j.val + 1)) D.host.E := X.submatrix id (Fin.castLE j.2)

def root (t : Fin r → ℝ) (j : Fin r) : ℝ := if h : j.val + 1 < r then t j / t ⟨j.val + 1, h⟩ else t j

theorem isIsoFrame_firstCols {X Y : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) : IsIsoFrame V (firstCols X j) := by
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · have h1 : LinearIndependent D.host.E (fun i : Fin r => fun a : Fin V.rank => X a i) := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      have h3 : ∀ a, ∑ l, g l * X a l = 0 := fun a => by
        have := congrFun hg a
        simpa [Finset.sum_apply, mul_comm] using this
      have h4 : (fun l => (D.sp.cm.sig : D.host.E →+* D.host.E) (g l)) ᵥ*
          Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X = 0 := by
        funext a
        have := congrArg (D.sp.cm.sig : D.host.E →+* D.host.E) (h3 a)
        simp only [map_sum, map_mul, map_zero] at this
        simpa [Matrix.vecMul, dotProduct, Formalism.UG.cT] using this
      have h5 := congrArg (fun v => v ᵥ* (V.gram * Y)) h4
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul, ← Matrix.mul_assoc, hW.xy, Matrix.vecMul_one] at h5
      have h6 := congrFun h5 i
      simpa using h6
    have h2 : (firstCols X j).transpose = (fun i : Fin r => fun a : Fin V.rank => X a i) ∘ Fin.castLE j.2 := by
      funext i a; rfl
    change LinearIndependent D.host.E (firstCols X j).transpose
    rw [h2]
    exact h1.comp _ (Fin.castLE_injective _)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE j.2 a)) (Fin.castLE j.2 b)
    simpa [Matrix.mul_apply, Formalism.UG.cT, firstCols] using this

end GlobalTheory.CompanionTheory.RegInt
