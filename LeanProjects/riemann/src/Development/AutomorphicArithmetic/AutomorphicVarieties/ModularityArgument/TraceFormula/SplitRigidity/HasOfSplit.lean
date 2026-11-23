import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigid
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeak
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.UnitOf

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Tf.SR

theorem has_of_split {E : Type} [Field E] [NumberField E] [IsCMField E] (hE : GlobalTheory.BCT.Unr E) {n : ℕ} (hn : 1 ≤ n) (π : CuspSub E n)
    (hd : GlobalTheory.ContraPair.DualIsConj π) (D : CD E n) (hr : D.Reg)
    (hs : ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B) : D.Has π := by
  refine splitRigid E hE n hn (CG.mk π) (unitOf E n hn π hd) (Fin D.c) D.N D.P D.pos (fun i => ?_) (hs.mono fun w hw h => ?_)
  · obtain ⟨P, e, -, hu⟩ := partNorm absInf E n hn π hd D hr hs i
    exact e ▸ (CG.isUnitary_mk P).2 hu
  · obtain ⟨B, ⟨b, hb, rfl⟩, hB⟩ := hw h
    exact ⟨b, hb, hB⟩

def DescWeakAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU σ w) ∧
      ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ),
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B

theorem descWeakAll : DescWeakAll := fun E _ _ _ hE n hn π hreg hd hs =>
  (runTh E hE n hn π hreg hd hs).resolve_right fun ⟨D, h1, h2, _, h4⟩ => h1 (has_of_split hE hn π hd D h2 h4)

theorem descWeak : UpperTheory.V.Z.Desc.DescWeak := fun E _ _ _ hunr _ _ _ _ hsp _ n hn _ π hreg hd hsat =>
  descWeakAll E hunr n (le_trans one_le_two hn) π hreg hd fun w hw => hsat w fun h => hw (hsp w h)

end UpperTheory.V.Z.Tf.SR
