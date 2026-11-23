import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.InertBaseP

theorem exists_real (E : Type) [Field E] [NumberField E] [IsCMField E] (y : E)
    (hy : IsCMField.complexConj E y = y) :
    ∃ p : maximalRealSubfield E, algebraMap (maximalRealSubfield E) E p = y := by
  have h := (IsCMField.complexConj_eq_self_iff (K := E) (x := y)).1 hy
  exact ⟨⟨y, h⟩, rfl⟩

theorem decomp (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E) (hs : s ≠ 0)
    (hcs : IsCMField.complexConj E s = -s) (x : E) :
    ∃ p q : maximalRealSubfield E, x = algebraMap _ E p + s * algebraMap _ E q := by
  obtain ⟨p, hp⟩ := exists_real E ((x + IsCMField.complexConj E x) / 2) (by
    rw [map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat]; ring)
  obtain ⟨q, hq⟩ := exists_real E ((x - IsCMField.complexConj E x) / (2 * s)) (by
    rw [map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcs]
    field_simp; ring)
  refine ⟨p, q, ?_⟩
  rw [hp, hq]; field_simp; ring

end CompanionTheory.Rg.BcB.G3.InertBaseP

namespace CompanionTheory.Rg.BcB.G3

theorem inertBase_pf (h1 : TensorCompl) : InertBase := by
  intro E _ _ _ hU s d hs hcs hd w hw
  obtain ⟨hcont, -, -, hin, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨hconj, -⟩ := hin hw
  have h : w.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := rfl
  have hc2 := GlobalTheory.LFun.SplitChart.continuous_complMap (E := E) h
  refine ⟨GlobalTheory.LFun.complMap h, fun x => GlobalTheory.LFun.complMap_algebraMap h x, fun x => ?_, fun z => ?_⟩
  · have heq := (HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield E)
        (w.under (𝓞 (maximalRealSubfield E)))).equalizer (hcont.comp hc2) hc2 (funext fun a => by
          simp only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hconj, AlgEquiv.commutes])
    exact congrFun heq x
  · obtain ⟨t, rfl⟩ := GlobalTheory.LFun.ConjPlace.toCompl_surjective h z
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul a x =>
      obtain ⟨p, q, hx⟩ := InertBaseP.decomp E s hs hcs x
      refine ⟨a * algebraMap _ _ p, a * algebraMap _ _ q, ?_⟩
      simp only [GlobalTheory.LFun.toCompl_tmul, hx, map_mul, map_add, GlobalTheory.LFun.complMap_algebraMap]
      ring
    | add t1 t2 e1 e2 =>
      obtain ⟨a1, b1, f1⟩ := e1
      obtain ⟨a2, b2, f2⟩ := e2
      exact ⟨a1 + a2, b1 + b2, by rw [map_add, f1, f2, map_add, map_add]; ring⟩

end CompanionTheory.Rg.BcB.G3

end
