import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BadEx2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBPf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemULOfSplit

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.Bc.ArchbcB.B
open PositivityTheory.Rg.BcB.F.Ex0
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Ex0.BadSplitP

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isLevel_of_isCong {n m : ℕ} {w : Pl E} {KB : Subgroup (UL n w)} (hKB : IsCong m KB) :
    GlobalTheory.BCT.IsLevel (MonoidHom.id (UL n w)) (KL n w) KB := by
  have e : KB = (GlobalTheory.PrincCong.congSub w n m).subgroupOf (UL n w) := by
    ext k
    rw [Subgroup.mem_subgroupOf, GlobalTheory.PrincCong.mem_congSub_iff, hKB k]
    exact Iff.rfl
  rw [e]
  refine ⟨?_, fun k hk => ?_, fun k hk => hk⟩
  · rw [Subgroup.coe_subgroupOf]
    exact (GlobalTheory.PrincCong.isOpen_congSub w n m).preimage continuous_subtype_val
  · exact Subgroup.mem_subgroupOf.2 ((GlobalTheory.PrincCong.mem_congSub_iff w n m _).1 (Subgroup.mem_subgroupOf.1 hk)).1

end PositivityTheory.Rg.BcB.F.Ex0.BadSplitP

namespace PositivityTheory.Rg.BcB.F.Ex0

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem badSplit2 (h3 : M3) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n a : ℕ), a ≤ n →
    ∀ (w : Pl E), IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen (μ.ker : Set (w.adicCompletion E)ˣ) →
    ∀ m : ℕ, 1 ≤ m → ∀ KB : Subgroup (UL n w), IsCong m KB →
    ∃ L : Subgroup (GLw a w × GLw (n - a) w), IsPairLevel L ∧ IsHecke L (fixFn n a w μ m KB) ∧
      Match n a (n - a) w μ (U.lone KB) (fixFn n a w μ m KB) := by
  intro E _ _ _ hE n a ha w hw μ hμ m _ KB hKB
  have hK := BadSplitP.isLevel_of_isCong hKB
  have e : fixFn n a w μ m KB = ctMu (Nat.add_sub_cancel' ha) w μ (U.lone KB) := by
    unfold fixFn
    rw [dif_pos ha, if_pos hw]
  have hH : IsHecke KB (U.lone KB) := MB.mb_isHecke_lone hK (MB.mb_isCompact_KL_split hw)
  obtain ⟨K₁, K₂, h1, h2, -, hf⟩ := GlobalTheory.BCT.CtLevel.ctMu_hecke E hE n a ha w hw μ hμ KB hK
  rw [e]
  exact ⟨K₁.prod K₂, ⟨K₁, K₂, rfl, h1, h2⟩, (hf _ hH).1, h3 E n a ha w hw μ KB hK _ hH⟩

end PositivityTheory.Rg.BcB.F.Ex0

end
