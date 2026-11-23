import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormLelong
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSectionHyperplaneAvoid
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PDivCyclePrime
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

theorem FormIntLelong.proof (hCP : ConeToProjective.Statement)
    (hCh : ChowFormSectionAlgClosed.Statement) (hFS : FormIntSlice.Statement)
    (hSL : SliceFormLelong.Statement) : FormIntLelong.Statement := by
  intro n e h W u u' δ hW hg hu' hδ
  obtain ⟨F, hF⟩ := hg
  obtain ⟨ℓ, hℓW, hℓP⟩ := SectionHyperplaneAvoid.proof n W u' hW
  have ha0 : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → fsLogReg h u δ (t • x) = fsLogReg h u δ x :=
    fun t x ht => fsLogReg_smul h u δ t x ht
  have ha1 : ContDiffOn ℝ ∞ (fsLogReg h u δ) {x | x ≠ 0} := contDiffOn_fsLogReg h u hδ

  have hWc := hCP n (e + 1) h W F ℓ (fsLogReg h u δ) hW hF hℓW ha0 ha1.continuousOn

  obtain ⟨c, -, gP, hgP, -⟩ := hCh ℂ n (e + 1) W F u' hW hF hu'
  have hcyc : cycleIntegral h (divCycle W u') e (fsLogReg h u δ) =
      ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fsLogReg h u δ)
          (fun _ x => Real.log (h.dualNorm x)) := by
    unfold cycleIntegral
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hCP n e h P (gP P) ℓ (fsLogReg h u δ) (DivCyclePrime.proof n W u' hW P hP) (hgP P hP)
      (hℓP P hP) ha0 ha1.continuousOn]
  rw [hcyc, hWc]

  refine (hSL n e h W F u' ℓ (fsLogReg h u δ) hW hF hu' hℓW hℓP ha0 ha1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hFS n e h W F ℓ (fsLogReg h u δ) (fsLogReg h u' ε) hW hF hℓW ha0 ha1.continuousOn
    (fun t x ht => fsLogReg_smul h u' ε t x ht) (contDiffOn_fsLogReg h u' hε)).symm

end GroundTheory.Heights₂.Heights
