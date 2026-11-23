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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols
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
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

theorem mem_parRat_frameFlag_firstCols : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) (δ : GF V),
    (∀ l : Fin r, l ≤ j → ∃ b : Fin r → D.host.E, δ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) →
    δ ∈ (frameFlag (isIsoFrame_firstCols hW j)).parRat D.sp.cm := by
  intro D V r X Y hW j δ h
  have hcoord : ∀ c : Fin V.rank → D.host.E, ratAct D.sp.cm V δ (GlobalTheory.AutFunCompare.vecOf V c) =
      GlobalTheory.AutFunCompare.vecOf V (δ.1.1 *ᵥ c) := by
    intro c
    refine V.frame.ext_elem fun i => ?_
    rw [GlobalTheory.AutFunCompare.repr_vecOf, ratAct, Matrix.repr_toLin]
    congr 1
    funext a
    exact GlobalTheory.AutFunCompare.repr_vecOf V c a
  have hspan : ∀ x ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j),
      ratAct D.sp.cm V δ x ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j) := by
    have hle : GlobalTheory.AutFunCompare.colSpan V (firstCols X j) ≤
        (GlobalTheory.AutFunCompare.colSpan V (firstCols X j)).comap (ratAct D.sp.cm V δ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      obtain ⟨b, hb, hb0⟩ := h (Fin.castLE j.2 k) (Nat.lt_succ_iff.1 k.2)
      have hcol : (firstCols X j)ᵀ k = fun a => X a (Fin.castLE j.2 k) := rfl
      change ratAct D.sp.cm V δ (GlobalTheory.AutFunCompare.vecOf V ((firstCols X j)ᵀ k)) ∈ GlobalTheory.AutFunCompare.colSpan V (firstCols X j)
      rw [hcoord, hcol, hb]
      have hsum : X *ᵥ b = ∑ l, b l • (fun a => X a l) := by
        funext a
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [hsum, GlobalTheory.AutFunCompare.vecOf, map_sum]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [map_smul]
      by_cases hl : l ≤ j
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l.val, Nat.lt_succ_iff.2 hl⟩, rfl⟩)
      · rw [hb0 l (not_le.1 hl), zero_smul]
        exact Submodule.zero_mem _
    exact fun x hx => hle hx
  change GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.diagH D.sp.cm.sig V.gram D.host.F δ ∈ IsoFlag.par _ D.sp.cm D.host.F
  rw [frameFlag, IsoFlag.par_single, diagH_mem_parab]
  exact hspan

end GlobalTheory.CompanionTheory.RegInt
