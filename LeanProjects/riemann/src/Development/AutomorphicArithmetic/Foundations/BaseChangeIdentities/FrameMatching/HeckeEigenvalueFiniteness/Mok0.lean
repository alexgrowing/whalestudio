import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem mok0 {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) : MLM.MOk F₀.d₀ := by
  have h0 : ∀ w, w ∉ F₀.d₀.T := fun w => by rw [F₀.T₀]; exact Finset.notMem_empty w
  have hlev : ∀ w ∈ F₀.d₀.Bad, GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (F₀.d₀.KB w) := fun w hw => by
    have h := F₀.levFam.1 w
    have e : F₀.d₀.KU w = F₀.d₀.KB w :=
      (if_neg (h0 w)).trans ((if_neg fun h' => Finset.disjoint_left.1 F₀.ok₀.disj.2.2 h' hw).trans (if_pos hw))
    rwa [e] at h
  refine ⟨fun w hw => absurd hw (h0 w), fun w hw => ⟨(F₀.S₀ w hw).2, fun g => ?_, F₀.K'_lev w hw⟩,
    fun w hw hs => ⟨hlev w hw, fun a ha => ?_⟩, fun w hw hs => ⟨F₀.kB w, F₀.kB_pos w hw hs, hlev w hw, fun γ => ?_, fun a ha => ?_⟩⟩
  · unfold UL
    rw [if_pos (F₀.S₀ w hw).2]
    exact Subgroup.mem_top g
  · rw [F₀.fix_def a ha w, if_pos hw, if_pos hs]
  · have e : {γ : UL n w | γ.1 ∈ MB.congK n w (F₀.kB w)} =
        (((GlobalTheory.PrincCong.congSub w n (F₀.kB w)).subgroupOf (UL n w) : Subgroup (UL n w)) : Set (UL n w)) :=
      Set.ext fun x => (GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) x.1).symm
    rw [F₀.KB_def w, if_pos hw, if_neg hs, e, Subgroup.closure_eq]
    exact GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) γ.1
  · rw [F₀.fix_def a ha w, if_pos hw, if_neg hs]

end UpperTheory.HeckeLevelFrameExistence

end
