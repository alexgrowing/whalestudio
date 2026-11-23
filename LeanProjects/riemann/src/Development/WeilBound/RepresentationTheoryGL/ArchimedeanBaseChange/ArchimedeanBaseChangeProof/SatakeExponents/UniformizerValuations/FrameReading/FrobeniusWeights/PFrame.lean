import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FRGood

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.FG

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem frGoodOf_holds : FRGoodOf := by
  intro h1 h2 hR E _ _ _ hE n π hπ S T F₀ F i s₁ s₂ Pa Pb D hc A G h0 hG hl he
  obtain ⟨e1, e2, e3, e4, -⟩ := F.same
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := fun w hw => F.levOff.1 (Finset.mem_coe.2 (Finset.mem_union_left _ hw))
  obtain ⟨l1, l2, -⟩ := h2 E n F₀.Sec F.d (F₀.C.a i) (F₀.C.le i) F₀.hSec F.ok hP
  exact h1 E hE n (F₀.C.a i) (F₀.C.le i) π hπ F₀.μ F₀.e F₀.hμ F₀.Sec F₀.hSec F.d F.ok hP
    (fun w => (congrFun e3 w).trans (F₀.μloc w)) (fun w => by rw [e4]; exact (F₀.unif w).2)
    (fun w hw a b => (F₀.good w hw (e1 ▸ a) (e2 ▸ b)).2) (F.fam.σ F.i₀)
    (fun w hw => ⟨F.comp w hw, ((F.fam.comp F.i₀).2.2.2 w hw).2.1⟩) _ _ _ _ _ _ (F₀.A i) s₁ s₂ Pa Pb D hc l1 l2 A G h0 hG hl
    fun w hw hg k intersection_update_fsHerm_neg_one => he (⟨w, hw, hg⟩, k, intersection_update_fsHerm_neg_one)

set_option maxHeartbeats 1000000 in
theorem frWeightOf_holds : FRWeightOf := by
  intro h1 hR E _ _ _ hE n hn π hπ S F₀ d i s₁ s₂ Pa Pb D hc
  obtain ⟨G, hG, h0, -⟩ := hc.vec
  exact h1 E hE n hn π hπ F₀.μ F₀.e F₀.hμ F₀.lam F₀.hlam _ _ (F₀.C.l₁ i) (F₀.C.l₂ i) (F₀.C.inf i) s₁ s₂ Pa Pb D hc.ctx
    hc.inf₁ hc.inf₂ ⟨G, hG, h0⟩

end PositivityTheory.Rg.BcB.F.FG

end
