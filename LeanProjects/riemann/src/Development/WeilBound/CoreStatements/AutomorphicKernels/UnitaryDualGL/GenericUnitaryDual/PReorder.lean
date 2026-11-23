import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.AddOneLeOfPrecedes
import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentProductEquivalence.CsReorderord
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reorder {h N : ℕ} (δ : Fin h → IrrGL k) (Δ : Fin h → Segment k) (s : Fin h → ℝ)
    (hL : ∀ j, IsLSeg (Δ j) (δ j).rep) (hc : ∀ j, PositivityTheory.UdReth2.IsCentred (Δ j)) (hs : ∀ j, |s j| < 1 / 2)
    (σ : Equiv.Perm (Fin h)) (hd : ∑ j, ((δ j).nu (s j)).1 = N) (hd' : ∑ j, ((δ (σ j)).nu (s (σ j))).1 = N) :
    Nonempty ((prodIrr (fun j => (δ j).nu (s j)) hd).Equiv (prodIrr (fun j => (δ (σ j)).nu (s (σ j))) hd')) := by
  have hnp : ∀ i j, ¬ ((Δ i).nu ((s i : ℝ) : ℂ)).Precedes ((Δ j).nu ((s j : ℝ) : ℂ)) := by
    intro i j hp
    have h1 := PositivityTheory.UdReth2.add_one_le_of_precedes (Δ i) (Δ j) (hc i) (hc j) (s i) (s j) hp
    have := hs i
    have := hs j
    rw [abs_lt] at *
    linarith
  exact PositivityTheory.PfEss.Zc2.cs_reorderord PositivityTheory.RgGu.NR.ConjDual.irrAdm' (GlobalTheory.RgGu.Holds.lUnlinkedComm_holds k)
    (fun j => (Δ j).nu ((s j : ℝ) : ℂ)) σ (fun j => (δ j).nu (s j)) hd hd'
    (fun i j _ => hnp i j) (fun i j _ => hnp (σ i) (σ j)) (fun j => GlobalTheory.isLSeg_nu (hL j) _)

end PositivityTheory.Gud.Pf

end
