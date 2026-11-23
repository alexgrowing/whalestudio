import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.WeightLOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FG

open JetMatrixAlgebra GlobalTheory.ThetaSatake in
theorem conjFix_holds : ConjFix := by
  intro E _ _ _ a b
  refine ⟨fun w u G _ hwu hG => ?_, fun S hS => ⟨fun u hu => ?_, fun X => ?_⟩⟩
  · obtain ⟨x, rfl⟩ : ∃ x, cw x = w := ⟨cw w, GlobalTheory.ThetaPull.conjSrc_conjSrc w⟩
    obtain rfl : u = x := (GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hwu).trans (GlobalTheory.ThetaPull.conjSrc_conjSrc x)
    rw [pairRtT_cw] at hG
    refine (mem_fixed_comp_symm _ (fun g => ?_)).1 hG
    show g ∈ (KGL u a).prod (KGL u b) ↔ ((fx u a).prodCongr (fx u b)) g ∈ (KGL (cw u) a).prod (KGL (cw u) b)
    rw [Subgroup.mem_prod, Subgroup.mem_prod]
    exact and_congr (mem_fx_iff u a g.1) (mem_fx_iff u b g.2)
  · obtain ⟨w, ⟨hwS, hwu⟩, -⟩ := hS u
    by_cases h : w = u
    · exact Or.inl (h ▸ hwS)
    · exact Or.inr ⟨w, hwS, ⟨u, Ne.symm h, hwu.symm⟩, hwu.symm, Or.inl (Ne.symm h)⟩
  · refine (X.finite_toSet.image cw).subset fun u hu => ?_
    obtain ⟨w, hw, hwu⟩ := hu
    exact ⟨w, hw, (GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hwu).symm⟩

end PositivityTheory.Rg.BcB.F.FG

end
