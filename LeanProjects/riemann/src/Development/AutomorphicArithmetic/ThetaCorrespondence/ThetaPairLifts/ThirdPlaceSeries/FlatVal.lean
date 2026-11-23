import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.FlatVal
variable {D : D7} {L : SizeData₂ D}
theorem flat_val_alt : _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict ∧ (∀ q : ℕ, q.Prime → Y.d.l₂.GoodAt q) ∧ GlobalTheory.FlatLine.FlatExists Y.U (xiR (Fm.D x ι)) ∧ (∀ τ, |GlobalTheory.FlatLine.c1 Y.U (xiR (Fm.D x ι)) τ + (((dat p i).p : ℝ) - (dat p i).q) / 2 * (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| ≤ 3 * (dat p i).q * (Fm.L x ι).sc.L) ∧ GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes p.T.Q.H Y.d.l₂) ≤ 40 * (Fm.L x ι).sc.L := by
  intro hF
  refine Closed.imp (Closed.and hF (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0)) ?_
  rintro eps Fm CH _ ⟨⟨C, -, h1⟩, A, -, h2⟩
  obtain ⟨x0, h⟩ := h1.and h2
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨a, b⟩ := h x hx hle ι p hp
  have hN := b i
  have hD : GlobalTheory.FlatLine.FlatDegree Y.U _ _ := a i hi Y hY
  have hT := p.fw.laws
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hpos := Inhab.rank_pos _ hT.pins _ hj
  refine ⟨isComplexData hT hj hY.1, (GlobalTheory.LawsDeep.laws_deep _ _ _ Y _ _ hT hj hY.1).good, hD.flatExists, fun τ => ?_, ?_⟩
  · rw [hD.c1_eq (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Y.d.Xo₂ Y.d.c₂ hpos).1, hT.pins.1.1]
    have e : ∀ u v : ℝ, -u - v + u = -v := fun u v => by ring
    rw [e, abs_neg, abs_mul, Nat.abs_cast, mul_comm 3, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_log_sub_lrd_le hN) (Nat.cast_nonneg _)
  · exact (GlobalTheory.BadLog.logSum_le_log (GlobalTheory.BadLog.log_level_le (Fm.params x hx ι)).1
      fun q hq => GlobalTheory.BadLog.dvd_of_mem_badPrimes hT.pins hY.1 hq).trans (log_level_le (Fm.params x hx ι) hN)
end GlobalTheory.CovTop.FlatVal
end
end
