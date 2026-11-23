import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.WeightLOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.HcHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSat

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FG

theorem ctHecke_holds : CtHecke := by
  intro E _ _ _ n a b h w ν ϖ k hw hϖ hν
  have h0 : ϖ ≠ 0 := b_unif_ne_zero hϖ
  have hord : ordL ((Units.mk0 ϖ h0 : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [Units.val_mk0]; exact ordL_unif hϖ
  have hH := PositivityTheory.Rg.BcB.F.Fok.ctT_hecke E n a b h w ν (Units.mk0 ϖ h0) hw hord hν k
  rw [Units.val_mk0] at hH
  refine ⟨hH.1, fun y hy g => (hH.2 y hy g).2, ?_⟩
  have hm : ν (-1) = 1 := by
    apply hν
    have := ord_neg_one' (w := w)
    rwa [GlobalTheory.BCT.InertChar.ord_eq_ordL] at this
  rw [map_pow, hm, one_pow]

end PositivityTheory.Rg.BcB.F.FG

end
