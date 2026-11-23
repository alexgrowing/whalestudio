import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinrankLeRankOnAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

theorem diag_abstract_collisions_once :
    ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (one : H) (Pg B A₁ A₂ : ℝ), 0 ≤ Pg → X.AbsConv → X.NormExpansionOn X.genSet → X.NormExpansionOn X.ngSet → X.GGBound Pg → X.RowOrth → X.CorankPos → Formalism.L2.SG.RowsOther.IdOne X one → X.pairAbs (X.big X.nzSet) ≤ B → X.pairSum (X.one X.genSet) ≤ A₁ → X.pairSum (X.one X.ngSet) ≤ A₂ → ‖X.K0 - one‖ ^ 2 ≤ 2 * Pg * (B + A₁ + A₂) := by
  intro τ Rw I H H₁ _ _ _ _ _ _ X one Pg B A₁ A₂ hPg hA hNg hNn hG hO hC hI hB h1 h2
  have hE := Formalism.FourierDecayAlt.P.equal_index
  have hF := Formalism.FourierDecayAlt.P.subfamilyAlt τ Rw I H H₁ X hA
  obtain ⟨_, _, hng⟩ := Formalism.FourierDecayAlt.P.pair_split_alt τ Rw I H H₁ X hA hO hC

  have hgen : X.PhiEq X.genSet = X.pairSum (X.big X.genSet) + X.pairSum (X.one X.genSet) := by
    let Y : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁ := { X with scal := fun _ _ => True }
    obtain ⟨_, hg, _⟩ := Formalism.FourierDecayAlt.P.pair_split_alt τ Rw I H H₁ Y hA hO hC
    have e1 : Y.nsc Y.genSet = ∅ := by
      ext p; simp [Y, Formalism.FourierDecayAlt.PB.Terms.nsc]
    have e2 : Y.sc Y.genSet = X.one X.genSet := by
      ext p; simp [Y, Formalism.FourierDecayAlt.PB.Terms.sc, Formalism.FourierDecayAlt.PB.Terms.one, Formalism.FourierDecayAlt.PB.Terms.allPairs,
        Formalism.FourierDecayAlt.PB.Terms.genSet]
    have e0 : Y.pairSum ∅ = 0 := by simp [Formalism.FourierDecayAlt.PB.Terms.pairSum]
    rw [e1, e2, e0, add_zero] at hg
    exact hg

  have hS : Summable (fun p : τ × τ => ‖inner ℂ (X.vec p.1) (X.vec p.2)‖) := by
    have hv := hA.2.1
    have hm : Summable (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) :=
      hv.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_inner_le_norm _ _) hm
  have hdisj : Disjoint (X.big X.genSet) (X.big X.ngSet) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hq.1.1.2 hp.1.1.2
  have hunion : X.pairAbs (X.big X.genSet) + X.pairAbs (X.big X.ngSet) =
      X.pairAbs (X.big X.genSet ∪ X.big X.ngSet) := by
    unfold Formalism.FourierDecayAlt.PB.Terms.pairAbs
    rw [Set.indicator_union_of_disjoint hdisj]
    beta_reduce
    rw [Summable.tsum_add (hS.indicator _) (hS.indicator _), mul_add]
  have hsub : X.big X.genSet ∪ X.big X.ngSet ⊆ X.big X.nzSet := by
    rintro p (hp | hp)
    · exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.2⟩
    · exact ⟨⟨hp.1.1.1, hp.1.2.1.1, hp.1.2.2⟩, hp.2⟩
  have hsum : X.pairAbs (X.big X.genSet) + X.pairAbs (X.big X.ngSet) ≤ B := by
    rw [hunion]; exact (hF _ _ hsub).1.trans hB
  have bg : X.pairSum (X.big X.genSet) ≤ X.pairAbs (X.big X.genSet) :=
    (le_abs_self _).trans (hF _ _ le_rfl).2
  have bn : X.pairSum (X.big X.ngSet) ≤ X.pairAbs (X.big X.ngSet) :=
    (le_abs_self _).trans (hF _ _ le_rfl).2
  have g1 : ‖X.part X.genSet‖ ^ 2 ≤ Pg * (X.pairAbs (X.big X.genSet) + A₁) := by
    have := Formalism.FourierDecayAlt.P.price_of_index hE τ Rw I H H₁ X Pg X.genSet hNg hG
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hPg)
    rw [hgen]; linarith
  have g2 : ‖X.part X.ngSet‖ ^ 2 ≤ Pg * (X.pairAbs (X.big X.ngSet) + A₂) := by
    have := Formalism.FourierDecayAlt.P.price_of_index hE τ Rw I H H₁ X Pg X.ngSet hNn hG
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hPg)
    rw [hng]; linarith
  have hK : X.K0 - one = X.part X.genSet + X.part X.ngSet := by
    unfold Formalism.FourierDecayAlt.PB.Terms.K0
    rw [← hI]
    abel
  rw [hK]
  have hpar : ‖X.part X.genSet + X.part X.ngSet‖ ^ 2 ≤
      2 * ‖X.part X.genSet‖ ^ 2 + 2 * ‖X.part X.ngSet‖ ^ 2 := by
    have := norm_add_le (X.part X.genSet) (X.part X.ngSet)
    have h0 := norm_nonneg (X.part X.genSet + X.part X.ngSet)
    nlinarith [sq_nonneg (‖X.part X.genSet‖ - ‖X.part X.ngSet‖), norm_nonneg (X.part X.genSet),
      norm_nonneg (X.part X.ngSet)]
  have hfin : Pg * (X.pairAbs (X.big X.genSet) + A₁) + Pg * (X.pairAbs (X.big X.ngSet) + A₂) ≤
      Pg * (B + A₁ + A₂) := by
    rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ hPg; linarith
  linarith

end GlobalTheory
