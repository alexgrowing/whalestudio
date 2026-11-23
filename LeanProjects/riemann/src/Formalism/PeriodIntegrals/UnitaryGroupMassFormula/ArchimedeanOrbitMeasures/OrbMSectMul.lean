import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInf

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem mem_H_iff (h : GI X) :
    h ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') ↔
      h • ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) = ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) :=
  MulAction.mem_stabilizer_iff

theorem orbM_sect_mul (y : TupI X) (hy : ∃ g : GI X, orbM X u' g = y)
    (h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) :
    orbM X u' (sect X u' y * (h : GI X)) = y := by
  have e1 := sect_spec X u' y hy
  unfold orbM at e1 ⊢
  rw [mul_smul, (mem_H_iff X u' h).1 h.2, e1]

theorem sect_smul (g : GI X) (y : TupI X) (hy : ∃ t : GI X, orbM X u' t = y) :
    ∃ h0 : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'),
      sect X u' (g • y) = g * sect X u' y * (h0 : GI X) := by
  set Y := ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) with hY
  have e1 : sect X u' y • Y = y := sect_spec X u' y hy
  obtain ⟨t, ht⟩ := hy
  have e2 : sect X u' (g • y) • Y = g • y :=
    sect_spec X u' _ ⟨g * t, by rw [← ht]; exact mul_smul g t Y⟩
  set a := sect X u' y with ha
  set b := sect X u' (g • y) with hb
  refine ⟨⟨(g * a)⁻¹ * b, ?_⟩, ?_⟩
  · rw [mem_H_iff, mul_smul, e2]
    rw [← e1, show g • a • Y = (g * a) • Y from (mul_smul g a Y).symm, inv_smul_smul]
  · simp only [mul_inv_cancel_left]

theorem muH_preimage (μ : Measure (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')))
    [μ.IsMulLeftInvariant] (hne : μ ≠ 0)
    (h0 : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'))
    (S : Set (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'))) (hS : MeasurableSet S) :
    μ ((fun h => h0 * h) ⁻¹' S) = μ S := by
  have hm : μ.map (fun h => h0 * h) = μ := map_mul_left_eq_self μ h0
  have ha : AEMeasurable (fun h => h0 * h) μ := by
    by_contra hc
    rw [Measure.map_of_not_aemeasurable hc] at hm
    exact hne hm.symm
  rw [← Measure.map_apply_of_aemeasurable ha hS, hm]

end PI.AprimeInfW
