import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateCollisionRowBoundAtParametersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NondegenerateCollisionRowBoundAtParametersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CollisionAbsSumBoundOfTwoRowBoundsStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem collS_on : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ S : Set ℝ, AmpOn S → CountBoundOn S → SmallOn S → TieOn S → On S CollS := by
  intro hSMR S hAmp hCnt hSmall hTie
  intro Cg cb Cu cT CT hcb hcT
  obtain ⟨c3, cH, thr1, hC⟩ := hCnt Cg cb Cu cT CT
  obtain ⟨cV, thr2, hT⟩ := hTie Cg cb Cu cT CT
  obtain ⟨Ca, C2, Ch, -, hCh, hA⟩ := hAmp Cg cb Cu cT CT hcb hcT
  set c : ℝ := max (max (max (max c3 1) CT) (|cH| + 2)) (|cV| + 2) with hc
  have hc3 : c3 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcT' : CT ≤ c := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hcH : |cH| + 2 ≤ c := le_trans (le_max_right _ _) (le_max_left _ _)
  have hcV : |cV| + 2 ≤ c := le_max_right _ _
  set C : ℝ := max (max (max (max (max c (4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2))) (2 * C2)) |Ca|)
    (408 * (Real.exp 1 * Real.pi))) CT with hCdef
  have hCc : c ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC4 : 4 + (c ^ 2 + 2 * max (Ch - c) 0) * (6 * c + 2) ≤ C := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))))
  have hC2 : 2 * C2 ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCa : |Ca| ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC408 : 408 * (Real.exp 1 * Real.pi) ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCT : CT ≤ C := le_max_right _ _
  obtain ⟨thr3, hA3⟩ := hA (9 * c + 3) 1 one_pos
  obtain ⟨thr4, hS⟩ := hSmall Cg cb Cu cT CT 1 hcb hcT one_pos
  obtain ⟨thr5, hsum⟩ := GlobalTheory.T.collisionAbsSum_bound_of_two_rowBounds hSMR CT C hC408 hCT
  refine ⟨max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4), ?_⟩
  intro C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u hCG hTies hadm hH0 hConc hAbs
  have hle : ∀ {x : ℝ}, max (max (max (max (max thr1 thr2) thr3) thr4) thr5) (max (3 * |C2|) 4) ≤ x →
      thr1 ≤ x ∧ thr2 ≤ x ∧ thr3 ≤ x ∧ thr4 ≤ x ∧ thr5 ≤ x ∧ 3 * |C2| ≤ x ∧ 4 ≤ x := by
    intro x hx
    simp only [max_le_iff] at hx
    exact ⟨hx.1.1.1.1.1, hx.1.1.1.1.2, hx.1.1.1.2, hx.1.1.2, hx.1.2, hx.2.1, hx.2.2⟩
  obtain ⟨h1', h2', h3', h4', h5', h6', h7'⟩ := hle hC'
  obtain ⟨h1l, h2l, h3l, h4l, h5l, -, h7l⟩ := hle hCl
  have hCnt' := hC C0 hC0 C' Cl h1' h1l D large₂ u
  have hc3' := hCnt'.1 c hc3
  obtain ⟨T, Z, hTA, hVol⟩ := hT C0 hC0 C' Cl h2' h2l D large₂ X Y hF hI u hTies hH0 hConc
  have hAmpAt := hA3 C0 hC0 C' Cl h3' h3l D large₂ hCG hTies hadm hConc.2.2.2.2.2.2.2
  have hSm := hS C0 hC0 C' Cl h4' h4l D large₂ hTies hadm
  have hHyp : Cnt.Hyp D large₂ u u C' Cl Cg cb Cu cT CT C0 1 :=
    Formalism.MainNotions.count_hypotheses_diagonal_words D large₂ C' Cl Cg cb Cu cT CT C0 1 hH0.2.1 hH0.1 hH0.2.2 (by linarith) (by linarith) le_rfl u
  have hC2' : |C2| ≤ C' := by have := abs_nonneg C2; linarith
  have hDeg := GlobalTheory.T.degenerateCollision_rowBound_at_sizeData CT cH cV Ca C2 Ch c C hc1 hcT' hcH hcV hCh hCc hC4 hC2 hCa D large₂ u T Z C' Cl Cg cb Cu cT C0
    h6' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  have hND := GlobalTheory.T.nondegenerateCollision_rowBound_at_parameters CT cH cV Ca C2 Ch c C hc1 hcH hcV hCh hCc hC4 D large₂ u T Z C' Cl Cg cb Cu cT C0
    hC2' hHyp hc3' hCnt'.2 hVol hAmpAt hSm hTA.2.2.2.1 hTA.2.2.2.2.1 hTA.2.2.2.2.2.1
  exact hsum D large₂ X Y hF hI u T Z C' Cl Cg cb Cu cT C0 h5' h5l hH0 hConc hAbs hTA (hSm.2.2.2.2 hH0 u) hND hDeg

end GlobalTheory.Core.Deg
