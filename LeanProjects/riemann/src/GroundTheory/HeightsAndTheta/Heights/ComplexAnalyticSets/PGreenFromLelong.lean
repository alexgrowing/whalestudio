import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.MonotoneDoubleLimit
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDivCyclePrime
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProperSymm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology

theorem GreenFromLelong.proof (hS : FormIntSymm.Statement) (hP : FormIntPos.Statement)
    (hL : FormIntLelong.Statement) (hD : RegConeLimit.Statement)
    (hCh : ChowFormSectionAlgClosed.Statement) : GreenFromLelong.Statement := by
  intro _ _ _ _ _ _ n e h W u u' hW hg hu hu' hadm
  obtain ⟨g, hgc⟩ := hg

  have comps : ∀ v v' : Fin n → ℂ, linForm v ∉ W →
      (∀ W' ∈ (divCycle W v).support, linForm v' ∉ W') →
      Tendsto (fun δ => cycleIntegral h (divCycle W v) e (fsLogReg h v' δ)) (𝓝[>] 0)
        (𝓝 (cycleIntegral h (divCycle W v) e (fsLog h v'))) := by
    intro v v' hv hv'
    obtain ⟨c, -, gW, hgW, -⟩ := hCh ℂ n (e + 1) W g v hW hgc hv
    unfold cycleIntegral
    refine tendsto_finsetSum _ fun W' hW' => ?_
    exact (hD n e h W' v' (DivCyclePrime.proof n W v hW W' hW') ⟨gW W', hgW W' hW'⟩
      (hv' W' hW')).const_mul _
  have hadm' : ∀ W' ∈ (divCycle W u').support, linForm u ∉ W' :=
    ProperSymm.proof n W u u' hW hu hu' hadm
  have hg2 : ∃ g : MvPolynomial (Fin (e + 2) × Fin n) ℂ, IsChowForm W (e + 2) g := ⟨g, hgc⟩
  have hg1 : ∃ g : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℂ, IsChowForm W (e + 1 + 1) g := ⟨g, hgc⟩
  refine (iterLim_eq_of_monotone
    (T := fun ε δ => formInt h W e (fsLogReg h u δ) (fsLogReg h u' ε) +
      coneIntegral h W (e + 1) (fsLogReg h u δ) + coneIntegral h W (e + 1) (fsLogReg h u' ε))
    (A := fun δ => cycleIntegral h (divCycle W u') e (fsLogReg h u δ) +
      coneIntegral h W (e + 1) (fsLog h u'))
    (B := fun ε => cycleIntegral h (divCycle W u) e (fsLogReg h u' ε) +
      coneIntegral h W (e + 1) (fsLog h u)) ?_ ?_ ?_ ?_ ?_ ?_).symm
  ·
    intro δ hδ ε hε ε' hεε'
    have h1 := hP n e h W u' u δ ε ε' hW hg2 hδ hε hεε'
    rw [← hS n e h W u u' ε δ hW hg2 hε hδ, ← hS n e h W u u' ε' δ hW hg2 (hε.trans_le hεε') hδ] at h1
    linarith
  · intro ε hε δ hδ δ' hδδ'
    have h1 := hP n e h W u u' ε δ δ' hW hg2 hε hδ hδδ'
    linarith
  · intro δ hδ
    have := ((hL n e h W u u' δ hW hg2 hu' hδ).add_const
      (coneIntegral h W (e + 1) (fsLogReg h u δ))).add (hD n (e + 1) h W u' hW hg1 hu')
    convert this using 2
    ring
  · intro ε hε
    have := ((hL n e h W u' u ε hW hg2 hu hε).add (hD n (e + 1) h W u hW hg1 hu)).add_const
      (coneIntegral h W (e + 1) (fsLogReg h u' ε))
    refine Tendsto.congr' ?_ (by convert this using 2; ring)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [hS n e h W u u' ε δ hW hg2 hε hδ]
  · exact (comps u' u hu' hadm').add_const _
  · exact (comps u u' hu hadm).add_const _

end GroundTheory.Heights₂.Heights
